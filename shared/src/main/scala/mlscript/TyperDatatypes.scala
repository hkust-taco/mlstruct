package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

abstract class TyperDatatypes extends TyperHelpers { self: Typer =>
  
  type TN = TypeName
  
  
  // The data types used for type inference:
  
  case class TypeProvenance(loco: Opt[Loc], desc: Str, originName: Opt[Str] = N, isType: Bool = false) {
    val isOrigin: Bool = originName.isDefined
    def & (that: TypeProvenance): TypeProvenance = this // arbitrary; maybe should do better
    override def toString: Str = (if (isOrigin) "o: " else "") + "‹"+loco.fold(desc)(desc+":"+_)+"›"
  }
  type TP = TypeProvenance

  sealed abstract class TypeInfo

  /** A type for abstract classes that is used to check and throw
   * errors if the abstract class is being instantiated */
  case class AbstractConstructor(absMths: Set[Var], isTrait: Bool) extends TypeInfo
  
  /** A type that potentially contains universally quantified type variables,
    * and which can be isntantiated to a given level. */
  sealed abstract class TypeScheme extends TypeInfo {
    def uninstantiatedBody: SimpleType
    def instantiate(implicit lvl: Int): SimpleType
  }
  
  /** A type with universally quantified type variables
    * (by convention, those variables of level greater than `level` are considered quantified). */
  case class PolymorphicType(level: Int, body: SimpleType) extends TypeScheme {
    val prov: TypeProvenance = body.prov
    def uninstantiatedBody: SimpleType = body
    def instantiate(implicit lvl: Int): SimpleType = freshenAbove(level, body)
    def rigidify(implicit lvl: Int): SimpleType = freshenAbove(level, body, rigidify = true)
  }
  
  /** `body.get._1`: implicit `this` parameter
    * `body.get._2`: actual body of the method
    * `body` being `None` indicates an error:
    *   - when this MethodType is computed from `MethodSet#processInheritedMethods`,
    *     it means two or more parent classes defined or declared the method
    *     and the current class did not override it;
    *   - when this MethodType is obtained from the environment, it means the method is ambiguous,
    *     which happens when two or more unrelated classes define or declare a method with the same name.
    *     So note that in this case, it will have more than one parent.
    *   Note: This is some fairly brittle and error-prone logic, which would gain to be refactored.
    *     Especially aggravating is the fact that `toPT`/`bodyPT` return `errorType` when `body` is `None`,
    *     whereas this case should probably be checked and carefully considered in each call site.
    * `isInherited`: whether the method declaration comes from the intersection of multiple inherited declarations
   */
  case class MethodType(
    level: Int,
    body: Opt[(SimpleType, SimpleType)],
    parents: List[TypeName],
    isInherited: Bool,
  )(val prov: TypeProvenance) {
    def &(that: MethodType): MethodType = {
      require(this.level === that.level)
      MethodType(level, mergeOptions(this.body, that.body)((b1, b2) => (b1._1 & b2._1, b1._2 & b2._2)),
        (this.parents ::: that.parents).distinct, isInherited = true)(prov)
    }
    val toPT: PolymorphicType =
      body.fold(PolymorphicType(0, errType))(b => PolymorphicType(level, FunctionType(singleTup(b._1), b._2)(prov)))
    val bodyPT: PolymorphicType =
      body.fold(PolymorphicType(0, errType))(b => PolymorphicType(level, ProvType(b._2)(prov)))
  }
  
  /** A type without universally quantified type variables. */
  sealed abstract class SimpleType extends TypeScheme with SimpleTypeImpl {
    val prov: TypeProvenance
    def level: Int
    def uninstantiatedBody: SimpleType = this
    def instantiate(implicit lvl: Int) = this
    constructedTypes += 1
  }
  type ST = SimpleType
  
  sealed abstract class BasicType extends SimpleType
  
  sealed abstract class FunOrArrType extends BasicType
  
  sealed trait Factorizable extends SimpleType
  
  case class FunctionType(lhs: SimpleType, rhs: SimpleType)(val prov: TypeProvenance) extends FunOrArrType {
    lazy val level: Int = lhs.level max rhs.level
    override def toString = s"(${lhs match {
      case TupleType((N, f) :: Nil) => ""+f
      case lhs => lhs
    }} -> $rhs)"
  }
  
  case class RecordType(fields: List[(Var, FieldType)])(val prov: TypeProvenance) extends SimpleType {
    lazy val level: Int = fields.iterator.map(_._2.level).maxOption.getOrElse(0)
    def toInter: SimpleType =
      fields.map(f => RecordType(f :: Nil)(prov)).foldLeft(TopType: ST)(((l, r) => ComposedType(false, l, r)(noProv)))
    def mergeAllFields(fs: Iterable[Var -> FieldType]): RecordType = {
      val res = mutable.SortedMap.empty[Var, FieldType]
      fs.foreach(f => res.get(f._1) match {
        case N => res(f._1) = f._2
        case S(ty) => res(f._1) = ty && f._2
      })
      RecordType(res.toList)(prov)
    }
    def addFields(fs: Ls[Var -> FieldType]): RecordType = {
      val shadowing = fs.iterator.map(_._1).toSet
      RecordType(fields.filterNot(f => shadowing(f._1)) ++ fs)(prov)
    }
    def sorted: RecordType = RecordType(fields.sortBy(_._1))(prov)
    override def toString = s"{${fields.map(f => s"${f._1}: ${f._2}").mkString(", ")}}"
  }
  object RecordType {
    def empty: RecordType = RecordType(Nil)(noProv)
    def mk(fields: List[(Var, FieldType)])(prov: TypeProvenance = noProv): SimpleType =
      if (fields.isEmpty) ExtrType(false)(prov) else RecordType(fields)(prov)
  }
  
  sealed abstract class ArrayBase extends FunOrArrType {
    def inner: SimpleType
  }

  case class ArrayType(val inner: SimpleType)(val prov: TypeProvenance) extends ArrayBase {
    def level: Int = inner.level
    override def toString = s"Array‹$inner›"
  }

  case class TupleType(fields: List[Opt[Var] -> SimpleType])(val prov: TypeProvenance) extends ArrayBase {
    lazy val inner: SimpleType = fields.map(_._2).reduceLeftOption(_ | _).getOrElse(BotType)
    lazy val level: Int = fields.iterator.map(_._2.level).maxOption.getOrElse(0)
    lazy val toArray: ArrayType = ArrayType(inner)(prov)  // upcast to array
    override def toString =
      s"(${fields.map(f => s"${f._1.fold("")(_.name+": ")}${f._2},").mkString(" ")})"
  }
  
  /** Polarity `pol` being `true` means Bot; `false` means Top. These are extrema of the subtyping lattice. */
  case class ExtrType(pol: Bool)(val prov: TypeProvenance) extends SimpleType {
    def level: Int = 0
    override def toString = if (pol) "⊥" else "⊤"
  }
  /** Polarity `pol` being `true` means union; `false` means intersection. */
  case class ComposedType(pol: Bool, lhs: SimpleType, rhs: SimpleType)(val prov: TypeProvenance) extends SimpleType {
    def level: Int = lhs.level max rhs.level
    override def toString = s"($lhs ${if (pol) "|" else "&"} $rhs)"
  }
  case class NegType(negated: SimpleType)(val prov: TypeProvenance) extends SimpleType {
    def level: Int = negated.level
    override def toString = s"~(${negated})"
  }
  
  /** A proxy type is a derived type form storing some additional information,
   * but which can always be converted into an underlying simple type. */
  sealed abstract class ProxyType extends SimpleType {
    def level: Int = underlying.level
    def underlying: SimpleType
    override def toString = s"[$underlying]"
  }
  object ProxyType {
    def unapply(proxy: ProxyType): S[ST] =
      S(proxy.underlying)
  }
  
  /** The sole purpose of ProvType is to store additional type provenance info. */
  case class ProvType(underlying: SimpleType)(val prov: TypeProvenance) extends ProxyType {
    override def toString = s"[$underlying]"
    // override def toString = s"$underlying[${prov.desc.take(5)}]"
    // override def toString = s"$underlying[${prov.toString.take(5)}]"
    // override def toString = s"$underlying@${prov}"
    // override def toString = showProvOver(true)(""+underlying)
    
    // TOOD override equals/hashCode? — could affect hash consing...
    // override def equals(that: Any): Bool = super.equals(that) || underlying.equals(that)
    // override def equals(that: Any): Bool = unwrapProxies.equals(that)
  }
  
  type TR = TypeRef
  case class TypeRef(defn: TypeName, targs: Ls[SimpleType])(val prov: TypeProvenance) extends SimpleType {
    def level: Int = targs.iterator.map(_.level).maxOption.getOrElse(0)
    def expand(implicit ctx: Ctx): SimpleType = expandWith(paramTags = true)
    def expandWith(paramTags: Bool)(implicit ctx: Ctx): SimpleType = {
      val td = ctx.tyDefs(defn.name)
      require(targs.size === td.tparamsargs.size)
      lazy val tparamTags =
        if (paramTags) RecordType.mk(td.tparamsargs.map { case (tp, tv) =>
            val tvv = td.getVariancesOrDefault
            tparamField(defn, tp) -> FieldType(
              if (tvv(tv).isCovariant) BotType else tv,
              if (tvv(tv).isContravariant) TopType else tv)(prov)
          })(noProv)
        else TopType
      subst(td.kind match {
        case Als => td.bodyTy
        case Cls => clsNameToNomTag(td)(prov, ctx) & td.bodyTy & tparamTags
        case Trt => trtNameToNomTag(td)(prov, ctx) & td.bodyTy & tparamTags
      }, td.targs.lazyZip(targs).toMap) //.withProv(prov)
    }
    private var tag: Opt[Opt[ClassTag]] = N
    def mkTag(implicit ctx: Ctx): Opt[ClassTag] = tag.getOrElse {
      val res = ctx.tyDefs.get(defn.name) match {
        case S(td @ TypeDef(Cls, _, _, _, _, _, _, _, _)) => S(clsNameToNomTag(td)(noProv, ctx))
        case _ => N
      }
      tag = S(res)
      res
    }
    def mapTargs[R](pol: Opt[Bool])(f: (Opt[Bool], ST) => R)(implicit ctx: Ctx): Ls[R] = {
      val td = ctx.tyDefs(defn.name)
      td.tvarVariances.fold(targs.map(f(N, _))) { tvv =>
        assert(td.tparamsargs.sizeCompare(targs) === 0)
        (td.tparamsargs lazyZip targs).map { case ((_, tv), ta) =>
          tvv(tv) match {
            case VarianceInfo(true, true) =>
              f(N, TypeRange(BotType, TopType)(noProv))
            case VarianceInfo(co, contra) =>
              f(if (co) pol else if (contra) pol.map(!_) else N, ta)
          }
      }}
    }
    override def toString = showProvOver(false) {
      val displayName =
        if (primitiveTypes.contains(defn.name)) defn.name.capitalize else defn.name
      if (targs.isEmpty) displayName else s"$displayName[${targs.mkString(",")}]"
    }
  }
  
  sealed abstract class ObjectTag extends BasicType with Ordered[ObjectTag] {
    val id: SimpleTerm
    def compare(that: ObjectTag): Int = this.id compare that.id
  }
  
  case class ClassTag(id: SimpleTerm, parents: Set[TypeName])(val prov: TypeProvenance) extends ObjectTag {
    lazy val parentsST = parents.iterator.map(tn => Var(tn.name)).toSet[SimpleTerm]
    def glb(that: ClassTag): Opt[ClassTag] =
      if (that.id === this.id) S(this)
      else if (that.parentsST.contains(this.id)) S(that)
      else if (this.parentsST.contains(that.id)) S(this)
      else N
    def level: Int = 0
    override def toString = showProvOver(false)("#" + id.idStr + s"<${parents.map(_.show).mkString(",")}>")
  }
  
  case class TraitTag(id: SimpleTerm)(val prov: TypeProvenance) extends ObjectTag with Factorizable {
    def level: Int = 0
    override def toString = "#" + id.idStr
  }
  
  /** `TypeRange(lb, ub)` represents an unknown type between bounds `lb` and `ub`,
    * where `lb` is in negative position and `ub` is in positive position.
    * For this type to be meaningful, it is necessary that `lb` be a subtype of `ub` by construction.
    * Currently, there are essentially two ways these types are introduced:
    * - During type extrusion, when extruding a variable occurring in neutral position:
    *   here, we create a type bound to recover the polarity needed to do the extrusion.
    *   This is correct because the negative extrusion of a type should be a subtype of its positive extrusion.
    * - In user-entered wildcard types `?`, which are interpreted as `TypeRange(Bot, Top)`.
    *   These are also treated as definition-level existentials,
    *   in that when checking an inferred type against a signature, which is done in the `subsume` method,
    *   each wildcard or type range is replaced by a fresh type variable bounded between `lb` and `ub`
    *   (this happens in rigidification). */
  case class TypeRange(lb: SimpleType, ub: SimpleType)(val prov: TypeProvenance) extends SimpleType {
    def level: Int = lb.level max ub.level
    override def toString = s"$lb..$ub"
  }
  object TypeRange {
    final def mk(lb: SimpleType, ub: SimpleType, prov: TypeProvenance = noProv)(implicit ctx: Ctx): SimpleType =
      if ((lb is ub) || lb === ub || lb <:< ub && ub <:< lb) lb else (lb, ub) match {
        case (TypeRange(lb, _), ub) => mk(lb, ub, prov)
        case (lb, TypeRange(_, ub)) => mk(lb, ub, prov)
        case _ => TypeRange(lb, ub)(prov)
      }
  }
  
  /** This class represents either a normal record field OR a type paarameter in a class,
    *   which are encoded using fields.
    * The lower bound `lb` will only be non-bottom when the field is used as a type parameter. */
  case class FieldType(lb: SimpleType, ub: SimpleType)(val prov: TypeProvenance) {
    def level: Int = lb.level max ub.level
    def <:< (that: FieldType)(implicit ctx: Ctx, cache: MutMap[ST -> ST, Bool] = MutMap.empty): Bool =
      (that.lb <:< this.lb) && (this.ub <:< that.ub)
    def && (that: FieldType, prov: TypeProvenance = noProv): FieldType =
      FieldType(lb | that.lb, ub & that.ub)(prov)
    def || (that: FieldType, prov: TypeProvenance = noProv): FieldType =
      FieldType(lb & that.lb, ub | that.ub)(prov)
    def update(lb: SimpleType => SimpleType, ub: SimpleType => SimpleType): FieldType =
      FieldType(lb(this.lb), ub(this.ub))(prov)
    override def toString =
      if (lb === BotType) s"$ub" else s"$lb..$ub"
  }
  
  /** A type variable living at a certain polymorphism level `level`, with mutable bounds.
    * Invariant: Types appearing in the bounds never have a level higher than this variable's `level`. */
  final class TypeVariable(
      val level: Int,
      var lowerBounds: List[SimpleType],
      var upperBounds: List[SimpleType],
      val nameHint: Opt[Str] = N
  )(val prov: TypeProvenance) extends SimpleType with CompactTypeOrVariable with Ordered[TypeVariable] with Factorizable {
    private[mlscript] val uid: Int = { freshCount += 1; freshCount - 1 }
    lazy val asTypeVar = new TypeVar(L(uid), nameHint)
    def compare(that: TV): Int = this.uid compare that.uid
    
    def isRecursive_$(implicit ctx: Ctx) : Bool = (lbRecOccs_$, ubRecOccs_$) match {
      case (S(N | S(true)), _) | (_, S(N | S(false))) => true
      case _ => false
    } 
    /** None: not recursive in this bound; Some(Some(pol)): polarly-recursive; Some(None): nonpolarly-recursive.
      * Note that if we have something like 'a :> Bot <: 'a -> Top, 'a is not truly recursive
      *   and its bounds can actually be inlined. */
    private final def lbRecOccs_$(implicit ctx: Ctx): Opt[Opt[Bool]] =
      TupleType(lowerBounds.map(N -> _))(noProv).getVarsPol(S(true)).get(this)
    private final def ubRecOccs_$(implicit ctx: Ctx): Opt[Opt[Bool]] =
      TupleType(upperBounds.map(N -> _))(noProv).getVarsPol(S(false)).get(this)
    
    override def toString: String = showProvOver(false)(nameHint.getOrElse("α") + uid + "'" * level)
  }
  type TV = TypeVariable
  private var freshCount = 0
  def freshVar(p: TypeProvenance, nameHint: Opt[Str] = N, lbs: Ls[ST] = Nil, ubs: Ls[ST] = Nil)
        (implicit lvl: Int): TypeVariable =
    new TypeVariable(lvl, lbs, ubs, nameHint)(p)
  def resetState(): Unit = {
    freshCount = 0
  }
  trait CompactTypeOrVariable
  type PolarVariable = (TypeVariable, Boolean)
  
  case class NegVar(tv: TV) extends ProxyType with Factorizable {
    lazy val underlying: SimpleType = tv.neg()
    val prov = noProv
  }
  case class NegTrait(tt: TraitTag) extends ProxyType with Factorizable {
    lazy val underlying: SimpleType = tt.neg()
    val prov = noProv
  }
  
}
