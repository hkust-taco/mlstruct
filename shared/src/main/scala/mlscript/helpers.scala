package mlscript

import scala.util.chaining._
import scala.collection.mutable.{Map => MutMap, SortedMap => SortedMutMap, Set => MutSet, Buffer}
import scala.collection.immutable.SortedSet

import math.Ordered.orderingToOrdered

import mlscript.utils._, shorthands._


// Auxiliary definitions for types

abstract class TypeImpl extends Located { self: Type =>
  
  lazy val typeVarsList: List[TypeVar] = this match {
    case uv: TypeVar => uv :: Nil
    case Recursive(n, b) => n :: b.typeVarsList
    case _ => children.flatMap(_.typeVarsList)
  }

  /**
    * @return
    *  set of free type variables in type
    */
  lazy val freeTypeVariables: Set[TypeVar] = this match {
    case Recursive(uv, body) => body.freeTypeVariables - uv
    case t: TypeVar => Set.single(t)
    case _ => this.children.foldRight(Set.empty[TypeVar])((ty, acc) => ty.freeTypeVariables ++ acc)
  }
  
  def show: Str = showIn(ShowCtx.mk(this :: Nil), 0)
  
  private def parensIf(str: Str, cnd: Boolean): Str = if (cnd) "(" + str + ")" else str
  private def showField(f: Field, ctx: ShowCtx): Str = f match {
    case Field(_, ub) => ub.showIn(ctx, 0)
  }
  def showIn(ctx: ShowCtx, outerPrec: Int): Str = this match {
    case Top => "anything"
    case Bot => "nothing"
    case TypeName(name) => name
    case TypeTag(name) => "#"+name
    case uv: TypeVar => ctx.vs(uv)
    case Recursive(n, b) => parensIf(s"${b.showIn(ctx, 2)} as ${ctx.vs(n)}", outerPrec > 1)
    case Function(Tuple((N, l) :: Nil), r) => Function(l, r).showIn(ctx, outerPrec)
    case Function(l, r) => parensIf(l.showIn(ctx, 31) + " -> " + r.showIn(ctx, 30), outerPrec > 30)
    case Neg(t) => s"~${t.showIn(ctx, 100)}"
    case Record(fs) => fs.map { nt =>
        val nme = nt._1.name
        if (nme.isCapitalized) nt._2 match {
          case Field(N | S(Bot), Top) => s"$nme"
          case Field(S(lb), ub) if lb === ub => s"$nme = ${ub.showIn(ctx, 0)}"
          case Field(N | S(Bot), ub) => s"$nme <: ${ub.showIn(ctx, 0)}"
          case Field(S(lb), Top) => s"$nme :> ${lb.showIn(ctx, 0)}"
          case Field(S(lb), ub) => s"$nme :> ${lb.showIn(ctx, 0)} <: ${ub.showIn(ctx, 0)}"
        }
        else s"${nme}: ${showField(nt._2, ctx)}"
      }.mkString("{", ", ", "}")
    case Tuple(fs) =>
      fs.map(nt => s"${nt._1.fold("")(_.name + ": ")}${nt._2.showIn(ctx, 0)},").mkString("(", " ", ")")
    case Union(TypeName("true"), TypeName("false")) | Union(TypeName("false"), TypeName("true")) =>
      TypeName("bool").showIn(ctx, 0)
    // case Union(l, r) => parensIf(l.showIn(ctx, 20) + " | " + r.showIn(ctx, 20), outerPrec > 20)
    // case Inter(l, r) => parensIf(l.showIn(ctx, 25) + " & " + r.showIn(ctx, 25), outerPrec > 25)
    case c: Composed =>
      val prec = if (c.pol) 20 else 25
      val opStr = if (c.pol) " | " else " & "
      c.distinctComponents match {
        case Nil => (if (c.pol) Bot else Top).showIn(ctx, prec)
        case x :: Nil => x.showIn(ctx, prec)
        case _ =>
          parensIf(c.distinctComponents.iterator
            .map(_.showIn(ctx, prec))
            .reduce(_ + opStr + _), outerPrec > prec)
      }
    // 
    case Bounds(Bot, Top) => s"?"
    case Bounds(lb, ub) if lb === ub => lb.showIn(ctx, outerPrec)
    case Bounds(Bot, ub) => s".. ${ub.showIn(ctx, 0)}"
    case Bounds(lb, Top) => s"${lb.showIn(ctx, 0)} .."
    case Bounds(lb, ub) => s"${lb.showIn(ctx, 0)} .. ${ub.showIn(ctx, 0)}"
    // 
    case AppliedType(n, args) => s"${n.name}[${args.map(_.showIn(ctx, 0)).mkString(", ")}]"
    case Literal(IntLit(n)) => n.toString
    case Literal(DecLit(n)) => n.toString
    case Literal(StrLit(s)) => "\"" + s + "\""
    case Constrained(b, ws) => parensIf(s"${b.showIn(ctx, 0)}\n  where${ws.map {
      case (uv, Bounds(Bot, ub)) =>
        s"\n    ${ctx.vs(uv)} <: ${ub.showIn(ctx, 0)}"
      case (uv, Bounds(lb, Top)) =>
        s"\n    ${ctx.vs(uv)} :> ${lb.showIn(ctx, 0)}"
      case (uv, Bounds(lb, ub)) if lb === ub =>
        s"\n    ${ctx.vs(uv)} := ${lb.showIn(ctx, 0)}"
      case (uv, Bounds(lb, ub)) =>
        val vstr = ctx.vs(uv)
        s"\n    ${vstr             } :> ${lb.showIn(ctx, 0)}" +
        s"\n    ${" " * vstr.length} <: ${ub.showIn(ctx, 0)}"
    }.mkString}", outerPrec > 0)
    case Literal(UnitLit(b)) => if (b) "undefined" else "null"
  }
  
  def children: List[Type] = this match {
    case _: NullaryType => Nil
    case Function(l, r) => l :: r :: Nil
    case Bounds(l, r) => l :: r :: Nil
    case Neg(b) => b :: Nil
    case Record(fs) => fs.flatMap(f => f._2.in.toList ++ (f._2.out :: Nil))
    case Tuple(fs) => fs.unzip._2
    case Union(l, r) => l :: r :: Nil.toList
    case Inter(l, r) => l :: r :: Nil
    case Recursive(n, b) => b :: Nil
    case AppliedType(n, ts) => ts
    case Constrained(b, ws) => b :: ws.flatMap(c => c._1 :: c._2 :: Nil)
  }

  /**
    * Collect fields recursively during code generation.
    * Note that the type checker will reject illegal cases.
    */
  lazy val collectFields: Ls[Str] = this match {
    case Record(fields) => fields.map(_._1.name)
    case Inter(ty1, ty2) => ty1.collectFields ++ ty2.collectFields
    case _: Union | _: Function | _: Tuple | _: Recursive
        | _: Neg | _: Bounds | Top | Bot
        | _: Literal | _: TypeVar | _: AppliedType | _: TypeName | _: TypeName | _: TypeTag | _: Constrained =>
      Nil
  }

  /**
    * Collect `TypeName`s recursively during code generation.
    * Note that the type checker will reject illegal cases.
    */
  lazy val collectTypeNames: Ls[Str] = this match {
    case TypeName(name) => name :: Nil
    case AppliedType(TypeName(name), _) => name :: Nil
    case Inter(lhs, rhs) => lhs.collectTypeNames ++ rhs.collectTypeNames
    case _: Union | _: Function | _: Record | _: Tuple | _: Recursive
        | _: Neg | _: Bounds | Top | Bot | _: TypeTag
        | _: Literal | _: TypeVar | _: Constrained =>
      Nil
  }

  // Collect fields and types of record types that are intersected
  // by traversing the first level of intersection. This is used
  // for finding the fields and types of a class body, since the
  // body is made of up an intersection of classes and records
  lazy val collectBodyFieldsAndTypes: List[Var -> Type] = this match {
    case Record(fields) => fields.map(field => (field._1, field._2.out))
    case Inter(ty1, ty2) => ty1.collectBodyFieldsAndTypes ++ ty2.collectBodyFieldsAndTypes
    case _: Union | _: Function | _: Tuple | _: Recursive
        | _: Neg | _: Bounds | Top | Bot
        | _: Literal | _: TypeVar | _: AppliedType | _: TypeName | _: TypeTag | _: Constrained =>
      Nil
  }
}


final case class ShowCtx(vs: Map[TypeVar, Str])
object ShowCtx {
  /**
    * Create a context from a list of types. For named variables and
    * hinted variables use what is given. For unnamed variables generate
    * completely new names. If same name exists increment counter suffix
    * in the name.
    */
  def mk(tys: IterableOnce[Type], pre: Str = "'"): ShowCtx = {
    val (otherVars, namedVars) = tys.iterator.toList.flatMap(_.typeVarsList).distinct.partitionMap { tv =>
      tv.identifier match { case L(_) => L(tv.nameHint -> tv); case R(nh) => R(nh -> tv) }
    }
    val (hintedVars, unnamedVars) = otherVars.partitionMap {
      case (S(nh), tv) => L(nh -> tv)
      case (N, tv) => R(tv)
    }
    val usedNames = MutMap.empty[Str, Int]
    def assignName(n: Str): Str =
      usedNames.get(n) match {
        case S(cnt) =>
          usedNames(n) = cnt + 1
          pre + 
          n + cnt
        case N =>
          usedNames(n) = 0
          pre + 
          n
      }
    val namedMap = (namedVars ++ hintedVars).map { case (nh, tv) =>
      tv -> assignName(nh.dropWhile(_ === '\''))
      // tv -> assignName(nh.stripPrefix(pre))
    }.toMap
    val used = usedNames.keySet
    
    // * Generate names for unnamed variables
    val numLetters = 'z' - 'a' + 1
    val names = Iterator.unfold(0) { idx =>
      val postfix = idx/numLetters
      S(('a' + idx % numLetters).toChar.toString + (if (postfix === 0) "" else postfix.toString), idx + 1)
    }.filterNot(used).map(assignName)
    
    ShowCtx(namedMap ++ unnamedVars.zip(names))
  }
}

trait ComposedImpl { self: Composed =>
  val lhs: Type
  val rhs: Type
  def components: Ls[Type] = (lhs match {
    case c: Composed if c.pol === pol => c.components
    case _ => lhs :: Nil
  }) ::: (rhs match {
    case c: Composed if c.pol === pol => c.components
    case _ => rhs :: Nil
  })
  lazy val distinctComponents =
    components.filterNot(c => if (pol) c === Bot else c === Top).distinct
}

abstract class PolyTypeImpl extends Located { self: PolyType =>
  def children: List[Located] =  targs :+ body
  def show: Str = s"${targs.iterator.map(_.name).mkString("[", ", ", "] ->")} ${body.show}"
}

trait TypeVarImpl extends Ordered[TypeVar] { self: TypeVar =>
  def compare(that: TypeVar): Int = {
    (this.identifier.fold((_, ""), (0, _))) compare (that.identifier.fold((_, ""), (0, _)))
  }
}

// Auxiliary definitions for terms

trait PgrmImpl { self: Pgrm =>
  lazy val desugared: (Ls[Diagnostic] -> (Ls[TypeDef], Ls[Terms])) = {
    val diags = Buffer.empty[Diagnostic]
    val res = tops.flatMap { s =>
        val (ds, d) = s.desugared
        diags ++= ds
        d
    }.partitionMap {
      case td: TypeDef => L(td)
      case ot: Terms => R(ot)
    }
    diags.toList -> res
  }
  override def toString = tops.map("" + _ + ";").mkString(" ")
}

object OpApp {
  def apply(op: Str, trm: Term): Term = App(Var(op), trm)
  def unapply(trm: Term): Opt[Term -> Term] = trm |>? {
    case App(op, lhs)
      if op.toLoc.exists(l => lhs.toLoc.exists(l.spanStart > _.spanStart))
      => (op, lhs)
  }
}

trait DeclImpl extends Located { self: Decl =>
  val body: Located
  def showBody: Str = this match {
    case Def(_, _, rhs) => rhs.fold(_.toString, _.show)
    case td: TypeDef => td.body.show
  }
  def describe: Str = this match {
    case _: Def => "definition"
    case _: TypeDef => "type declaration"
  }
  def show: Str = showHead + (this match {
    case TypeDef(Als, _, _, _, _, _) => " = "; case _ => ": " }) + showBody
  def showHead: Str = this match {
    case Def(true, n, b) => s"rec def $n"
    case Def(false, n, b) => s"def $n"
    case TypeDef(k, n, tps, b, _, _) =>
      s"${k.str} ${n.name}${if (tps.isEmpty) "" else tps.map(_.name).mkString("[", ", ", "]")}"
  }
}

trait TypeNameImpl extends Ordered[TypeName] { self: TypeName =>
  def compare(that: TypeName): Int = this.name compare that.name
}

trait TermImpl extends StatementImpl { self: Term =>
  val original: this.type = this
  
  def describe: Str = this match {
    case IntLit(value) => "integer literal"
    case DecLit(value) => "decimal literal"
    case StrLit(value) => "string literal"
    case UnitLit(value) => if (value) "undefined literal" else "null literal"
    case Var(name) => "reference" // "variable reference"
    case Asc(trm, ty) => "type ascription"
    case Lam(name, rhs) => "lambda expression"
    case App(OpApp(Var("|"), lhs), rhs) => "type union"
    case App(OpApp(Var("&"), lhs), rhs) => "type intersection"
    case App(OpApp(op, lhs), rhs) => "operator application"
    case OpApp(op, lhs) => "operator application"
    case App(lhs, rhs) => "application"
    case Rcd(fields) => "record"
    case Sel(receiver, fieldName) => "field selection"
    case Let(isRec, name, rhs, body) => "let binding"
    case Tup((N, x) :: Nil) => x.describe
    case Tup((S(_), x) :: Nil) => "binding"
    case Tup(xs) => "tuple"
    case CaseOf(scrut, cases) =>  "`case` expression" 
    case Subs(arr, idx) => "array access"
  }
  
  override def toString: Str = this match {
    case IntLit(value) => value.toString
    case DecLit(value) => value.toString
    case StrLit(value) => '"'.toString + value + '"'
    case UnitLit(value) => if (value) "undefined" else "null"
    case Var(name) => name
    case Asc(trm, ty) => s"$trm : $ty"
    case Lam(name, rhs) => s"($name => $rhs)"
    case App(lhs, rhs) => s"($lhs $rhs)"
    case Rcd(fields) =>
      fields.iterator.map(nv =>
        nv._1.name + ": " + nv._2).mkString("{", ", ", "}")
    case Sel(receiver, fieldName) => receiver.toString + "." + fieldName
    case Let(isRec, name, rhs, body) =>
      s"(let${if (isRec) " rec" else ""} $name = $rhs; $body)"
    case Tup(xs) =>
      xs.iterator.map { case (n, t) =>
        n.fold("")(_.name + ": ") + t + "," }.mkString("(", " ", ")")
    case CaseOf(s, c) => s"case $s of $c"
    case Subs(a, i) => s"$a[$i]"
  }
  
}

trait LitImpl { self: Lit =>
  def baseClasses: Set[TypeName] = (this match {
    case _: IntLit => Set.single(TypeName("int")) + TypeName("number")
    case _: StrLit => Set.single(TypeName("string"))
    case _: DecLit => Set.single(TypeName("number"))
    case _: UnitLit => Set.empty[TypeName]
  }) + TypeName("Object")
}

trait VarImpl { self: Var =>
  def isPatVar: Bool =
    name.head.isLetter && name.head.isLower && name =/= "true" && name =/= "false"
}

trait SimpleTermImpl extends Ordered[SimpleTerm] { self: SimpleTerm =>
  def compare(that: SimpleTerm): Int = this.idStr compare that.idStr
  val idStr: Str = this match {
    case Var(name) => name
    case lit: Lit => lit.toString
  }
}

trait FieldImpl extends Located { self: Field =>
  def children: List[Located] =
    self.in.toList ::: self.out :: Nil
}

trait Located {
  def children: List[Located]
  
  private var spanStart: Int = -1
  private var spanEnd: Int = -1
  private var origin: Opt[Origin] = N
  
  def withLoc(s: Int, e: Int, ori: Origin): this.type = {
    // assert(origin.isEmpty)
    origin = S(ori)
    // assert(spanStart < 0)
    // assert(spanEnd < 0)
    spanStart = s
    spanEnd = e
    this
  }
  def withLoc(loco: Opt[Loc]): this.type = {
    loco.foreach { that =>
      spanStart = that.spanStart
      spanEnd = that.spanEnd
      origin = S(that.origin)
    }
    this
  }
  def withLocOf(that: Located): this.type = withLoc(that.toLoc)
  def hasLoc: Bool = origin.isDefined
  lazy val toLoc: Opt[Loc] = getLoc
  private def getLoc: Opt[Loc] = {
    def subLocs = children.iterator.flatMap(_.toLoc.iterator)
    if (spanStart < 0) spanStart =
      subLocs.map(_.spanStart).minOption.getOrElse(return N)
    if (spanEnd < 0) spanEnd =
      subLocs.map(_.spanEnd).maxOption.getOrElse(return N)
    val origins = origin.fold(subLocs.map(_.origin).toList.distinct)(_ :: Nil)
    assert(origins.size === 1, origins)
    S(Loc(spanStart, spanEnd, origins.head))
  }
  /** Like toLoc, but we make sure the span includes the spans of all subterms. */
  def toCoveringLoc: Opt[Loc] = {
    def subLocs = (this :: children).iterator.flatMap(_.toLoc.iterator)
    val spanStart =
      subLocs.map(_.spanStart).minOption.getOrElse(return N)
    val spanEnd =
      subLocs.map(_.spanEnd).maxOption.getOrElse(return N)
    val origins = origin.fold(subLocs.map(_.origin).toList.distinct)(_ :: Nil)
    assert(origins.size === 1)
    S(Loc(spanStart, spanEnd, origins.head))
  }
}

trait DesugaredStatementImpl extends Located { self: DesugaredStatement =>
  def describe: Str
}

trait StatementImpl extends Located { self: Statement =>
  
  lazy val desugared = doDesugar
  private def doDesugar: Ls[Diagnostic] -> Ls[DesugaredStatement] = this match {
    case l @ LetS(isrec, pat, rhs) =>
      val (diags, v, args) = desugDefnPattern(pat, Nil)
      diags -> (Def(isrec, v, L(args.foldRight(rhs)(Lam(_, _)))).withLocOf(l) :: Nil)
    case t: Term => Nil -> (t :: Nil)
    case d: Decl => Nil -> (d :: Nil)
  }
  import Message._
  protected def desugDefnPattern(pat: Term, args: Ls[Term]): (Ls[Diagnostic], Var, Ls[Term]) = pat match {
    case App(l, r) => desugDefnPattern(l, r :: args)
    case v: Var => (Nil, v, args)
    case _ => (TypeError(msg"Unsupported pattern shape" -> pat.toLoc :: Nil) :: Nil, Var("<error>"), args)
  }
  
  def children: List[Located] = this match {
    case Var(name) => Nil
    case Asc(trm, ty) => trm :: Nil
    case Lam(lhs, rhs) => lhs :: rhs :: Nil
    case App(lhs, rhs) => lhs :: rhs :: Nil
    case Tup(fields) => fields.map(_._2)
    case Rcd(fields) => fields.map(_._2)
    case Sel(receiver, fieldName) => receiver :: fieldName :: Nil
    case Let(isRec, name, rhs, body) => rhs :: body :: Nil
    case LetS(_, pat, rhs) => pat :: rhs :: Nil
    case _: Lit => Nil
    case CaseOf(s, c) => s :: c :: Nil
    case d @ Def(_, n, b) => n :: d.body :: Nil
    case TypeDef(kind, nme, tparams, body, _, _) => nme :: tparams ::: body :: Nil
    case Subs(a, i) => a :: i :: Nil
  }
  
  
  override def toString: Str = this match {
    case LetS(isRec, name, rhs) => s"let${if (isRec) " rec" else ""} $name = $rhs"
    case _: Term => super.toString
    case d: Decl => d.show
  }
}

trait CaseBranchesImpl extends Located { self: CaseBranches =>
  
  def children: List[Located] = this match {
    case Case(pat, body, rest) => pat :: body :: rest :: Nil
    case Wildcard(body) => body :: Nil
    case NoCases => Nil
  }
  
  lazy val toList: Ls[Case] = this match {
    case c: Case => c :: c.rest.toList
    case _ => Nil
  }
  
}
