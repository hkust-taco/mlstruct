package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, ListSet}
import SortedSet.{empty => ssEmp}, ListSet.{empty => lsEmp}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

class NormalForms extends TyperDatatypes { self: Typer =>
  
  type PreserveTypeRefs >: Bool
  
  def preserveTypeRefs(implicit ptr: PreserveTypeRefs): Bool = ptr === true
  
  
  private def mergeTypeRefs(pol: Bool, trs1: ListSet[TR], trs2: ListSet[TR])(implicit ctx: Ctx): ListSet[TR] =
    // TODO we could do better by merging type arguments for variant type parameters
    trs1 ++ trs2
  
  
  sealed abstract class LhsNf {
    def toTypes: Ls[SimpleType] = toType() :: Nil
    def toType(sort: Bool = false): SimpleType =
      if (sort) mkType(true) else underlying
    private def mkType(sort: Bool): SimpleType = this match {
      case LhsRefined(bo, ft, at, ts, r, trs) =>
        val sr = if (sort) r.sorted else r
        val bo2 = bo.filter {
          case ClassTag(id, parents) => !trs.exists(_.defn.name === id.idStr)
          case _ => true
        } .fold(ft: Opt[ST])(bo => S(ft.fold(bo: ST)(bo & _)))
          .fold(at: Opt[ST])(bo => S(at.fold(bo: ST)(bo & _)))
        val trsBase = trs.iterator.foldRight(bo2.fold[ST](sr)(_ & sr))(_ & _)
        (if (sort) ts.toArray.sorted else ts.toArray).foldLeft(trsBase)(_ & _)
      case LhsTop => TopType
    }
    lazy val underlying: SimpleType = mkType(false)
    def level: Int = underlying.level
    def hasTag(ttg: TraitTag): Bool = this match {
      case LhsRefined(bo, ft, at, ts, r, trs) => ts(ttg)
      case LhsTop => false
    }
    def size: Int = this match {
      case LhsRefined(bo, ft, at, ts, r, trs) => bo.size + ft.size + at.size + ts.size + r.fields.size + trs.size
      case LhsTop => 0
    }
    def & (that: BasicType): Opt[LhsNf] = (this, that) match {
      case (LhsTop, that: TupleType) => S(LhsRefined(N, N, S(that), ssEmp, RecordType.empty, lsEmp))
      case (LhsTop, that: FunctionType) => S(LhsRefined(N, S(that), N, ssEmp, RecordType.empty, lsEmp))
      case (LhsTop, that: ArrayBase) => S(LhsRefined(N, N, S(that), ssEmp, RecordType.empty, lsEmp))
      case (LhsTop, that: ClassTag) => S(LhsRefined(S(that), N, N, ssEmp, RecordType.empty, lsEmp))
      case (LhsTop, that: TraitTag) => S(LhsRefined(N, N, N, SortedSet.single(that), RecordType.empty, lsEmp))
      case (LhsRefined(b1, f1, a1, ts, r1, trs), that: TraitTag) => S(LhsRefined(b1, f1, a1, ts + that, r1, trs))
      case (LhsRefined(b1, N, a1, ts, r1, trs), that: FunctionType) => S(LhsRefined(b1, S(that), a1, ts, r1, trs))
      case (LhsRefined(b1, S(FunctionType(lhs0, rhs0)), a1, ts, r1, trs), FunctionType(lhs1, rhs1)) =>
        S(LhsRefined(b1, S(FunctionType(lhs0 | lhs1, rhs0 & rhs1)(noProv)), a1, ts, r1, trs))
      case (LhsRefined(b1, f1, N, ts, r1, trs), that: ArrayBase) => S(LhsRefined(b1, f1, S(that), ts, r1, trs))
      case (LhsRefined(b1, f1, S(at), ts, r1, trs), that: ArrayBase) =>
        val res = (at, that) match {
          case (TupleType(fs0), tup @ TupleType(fs1)) =>
            if (fs0.size =/= fs1.size) return N
            S(TupleType(tupleIntersection(fs0, fs1))(noProv))
          case (ArrayType(ar), tup @ TupleType(fs)) =>
            S(TupleType(fs.map { ty => ty._1 -> (ar & ty._2) })(noProv))
          case (TupleType(fs), ArrayType(ar)) =>
            S(TupleType(fs.map { ty => ty._1 -> (ty._2 & ar) })(noProv))
          case (ArrayType(i1), ArrayType(i2)) =>
            S(ArrayType(i1 & i2)(noProv)) // * Array[p] & Array[q] => Array[p & q]
        }
        S(LhsRefined(b1, f1, res, ts, r1, trs))
      case (LhsRefined(N, f1, a1, ts, r1, trs), that: ClassTag) => S(LhsRefined(S(that), f1, a1, ts, r1, trs))
      case (LhsRefined(S(cls), f1, a1, ts, r1, trs), that: ClassTag) =>
        cls.glb(that).map(cls => LhsRefined(S(cls), f1, a1, ts, r1, trs))
    }
    def & (that: RecordType): LhsNf = this match {
      case LhsTop => LhsRefined(N, N, N, ssEmp, that, lsEmp)
      case LhsRefined(b1, f1, a1, ts, r1, trs) =>
        LhsRefined(b1, f1, a1, ts,
          RecordType(recordIntersection(r1.fields, that.fields))(noProv), trs)
    }
    def & (that: TypeRef)(implicit ctx: Ctx): Opt[LhsNf] = this match {
      case LhsTop => S(LhsRefined(N, N, N, ssEmp, RecordType.empty, ListSet.single(that)))
      case LhsRefined(b, f1, at, ts, rt, trs) =>
        val trs2 = trs + that // TODO again, could do better (by using `mergeTypeRefs`)
        val res = LhsRefined(b, f1, at, ts, rt, trs2)
        that.mkTag.fold(S(res): Opt[LhsNf])(res & _)
    }
    def & (that: LhsNf)(implicit ctx: Ctx): Opt[LhsNf] = (this, that) match {
      case (_, LhsTop) => S(this)
      case (LhsTop, _) => S(that)
      case (_, LhsRefined(bo, ft, at, ts, rt, trs)) =>
        val base1 = bo.fold(some(this & rt))(this & rt & _).getOrElse(return N)
        val base2 = ft.fold(some(base1))(ft => base1 & ft).getOrElse(return N)
        val base3 = at.fold(some(base2))(base2 & _)
        ts.iterator.foldLeft(
          trs.iterator.foldLeft(base3)(_.getOrElse(return N) & _)
        )(_.getOrElse(return N) & _)
    }
    def <:< (that: LhsNf): Bool = (this, that) match {
      case (_, LhsTop) => true
      case (LhsTop, _) => false
      case (LhsRefined(b1, f1, a1, ts1, rt1, trs1), LhsRefined(b2, f2, a2, ts2, rt2, trs2)) =>
        implicit val ctx: Ctx = Ctx.empty
        b2.forall(b2 => b1.exists(_ <:< b2)) &&
          f2.forall(f2 => f1.exists(_ <:< f2)) &&
          a2.forall(a2 => a1.exists(_ <:< a2)) &&
          ts2.forall(ts1) && rt1 <:< rt2 &&
          trs2.iterator.forall(tr2 => trs1.iterator.exists(_ <:< tr2))
    }
    def isTop: Bool = isInstanceOf[LhsTop.type]
  }
  case class LhsRefined(
      base: Opt[ClassTag],
      fun: Opt[FunctionType],
      arr: Opt[ArrayBase],
      ttags: SortedSet[TraitTag],
      reft: RecordType,
      trefs: ListSet[TypeRef]
  ) extends LhsNf {
    // assert(!trefs.exists(primitiveTypes contains _._1.name))
    override def toString: Str = s"${base.getOrElse("")}${fun.getOrElse("")}${arr.getOrElse("")}${reft}${
      (ttags.iterator ++ trefs.iterator).map("∧"+_).mkString}"
  }
  case object LhsTop extends LhsNf {
    override def toString: Str = "⊤"
  }
  
  
  sealed abstract class RhsNf {
    def toTypes: Ls[SimpleType] = toType() :: Nil
    def toType(sort: Bool = false): SimpleType =
      if (sort) mkType(true) else underlying
    private def mkType(sort: Bool): SimpleType = this match {
      case RhsField(n, t) => RecordType(n -> t :: Nil)(noProv)
      case RhsBases(ps, bf, trs) =>
        val sr = bf.fold(BotType: ST)(_.fold(identity, _.toType(sort)))
        val trsBase = trs.iterator.foldRight(sr)(_ | _)
        (if (sort) ps.sorted else ps).foldLeft(trsBase)(_ | _)
      case RhsBot => BotType
    }
    lazy val underlying: SimpleType = mkType(false)
    def level: Int = underlying.level
    def hasTag(ttg: ObjectTag): Bool = this match {
      case RhsBases(ts, _, trs) => ts.contains(ttg)
      case RhsBot | _: RhsField => false
    }
    def | (that: TypeRef)(implicit ctx: Ctx): Opt[RhsNf] = this match {
      case RhsBot => S(RhsBases(Nil, N, ListSet.single(that)))
      case RhsField(name, ty) => this | name -> ty
      case RhsBases(prims, bf, trs) =>
        val trs2 = trs + that // TODO again, could do better (by using `mergeTypeRefs`)
        S(RhsBases(prims, bf, trs2))
    }
    def | (that: RhsNf)(implicit ctx: Ctx): Opt[RhsNf] = that match {
      case RhsBases(prims, bf, trs) =>
        val thisWithTrs = trs.iterator.foldLeft(this)(_ | _ getOrElse (return N))
        val tmp = prims.foldLeft(thisWithTrs)(_ | _ getOrElse (return N))
        S(bf.fold(tmp)(_.fold(tmp | _ getOrElse (return N),
          tmp | _.name_ty getOrElse (return N))))
      case RhsField(name, ty) => this | name -> ty
      case RhsBot => S(this)
    }
    /** Tries to merge to RHS normal forms, which represent unions of basic components. */
    def tryMergeInter(that: RhsNf)(implicit ctx: Ctx): Opt[RhsNf] = (this, that) match {
      case (RhsBot, _) | (_, RhsBot) => S(RhsBot)
      case (RhsField(name1, ty1), RhsField(name2, ty2)) if name1 === name2 => S(RhsField(name1, ty1 && ty2))
      case (RhsBases(prims1, S(R(r1)), trs1), RhsBases(prims2, S(R(r2)), trs2))
        if prims1 === prims2 && trs1 === trs2 && r1.name === r2.name
        => S(RhsBases(prims1, S(R(RhsField(r1.name, r1.ty && r2.ty))), trs1))
      /* // * It is a bit complicated to merge unions of TypeRefs, so it's not currently done
      case (RhsBases(prims1, bf1, trs1), RhsBases(prims2, bf2, trs2))
        if prims1 === prims2 && bf1 === bf2
        && ??? // TODO determine when `mergeTypeRefs` can losslessly intersect these unions
        => // * eg for merging `~Foo[S] & ~Foo[T]`:
          S(RhsBases(prims1, bf1, mergeTypeRefs(false, trs1, trs2)))
      */
      case (RhsBases(prims1, bf1, trs1), RhsBases(prims2, bf2, trs2)) =>
        N // * Could do some more merging here – for the possible base types
      case _ => N
    }
    // * Could use inheritance hierarchy to better merge these
    def | (that: BasicType): Opt[RhsNf] = (this, that) match {
      case (RhsBot, p: ObjectTag) => S(RhsBases(p::Nil,N,lsEmp))
      case (RhsBot, that: FunOrArrType) => S(RhsBases(Nil,S(L(that)),lsEmp))
      case (RhsBases(ps, bf, trs), p: ClassTag) =>
        S(RhsBases(if (ps.contains(p)) ps else p :: ps , bf, trs))
      case (RhsBases(ps, N, trs), that: FunOrArrType) => S(RhsBases(ps, S(L(that)), trs))
      case (RhsBases(ps, S(L(t1@TupleType(fs1))), trs), t2@TupleType(fs2)) =>
        if (fs1.size =/= fs2.size) 
          RhsBases(ps, S(L(t1.toArray)), trs) | t2.toArray // * Upcast tuples of different sizes to array
        else S(RhsBases(ps, S(L(TupleType(fs1.lazyZip(fs2).map {
          case ((S(n1), ty1), (S(n2), ty2)) => (if (n1 === n2) S(n1) else N, ty1 | ty2)
          case ((n1o, ty1), (n2o, ty2)) => (n1o orElse n2o, ty1 | ty2)
        })(noProv))), trs))
      case (RhsBases(ps, S(L(ArrayType(_))), trs), t@TupleType(_)) => this | t.toArray
      case (RhsBases(ps, S(L(t@TupleType(_))), trs), ar@ArrayType(_)) => RhsBases(ps, S(L(t.toArray)), trs) | ar
      case (RhsBases(ps, S(L(ArrayType(ar1))), trs), ArrayType(ar2)) => 
        S(RhsBases(ps, S(L(ArrayType(ar1 | ar2)(noProv))), trs))
      case (RhsBases(ps, S(L(bt)), trs), _) if (that === bt) => S(this)
      case (RhsBases(ps, S(L(FunctionType(l0, r0))), trs), FunctionType(l1, r1)) =>
        S(RhsBases(ps, S(L(FunctionType(l0 & l1, r0 | r1)(noProv))), trs))
      case (RhsBases(ps, bf, trs), tt: TraitTag) =>
        S(RhsBases(if (ps.contains(tt)) ps else tt :: ps, bf, trs))
      case (f @ RhsField(_, _), p: ObjectTag) => S(RhsBases(p::Nil, S(R(f)), lsEmp))
      case (f @ RhsField(_, _), _: FunctionType | _: ArrayBase) =>
        // S(RhsBases(Nil, S(that), S(f)))
        N // can't merge a record and a function or a tuple -> it's the same as Top
        // NOTE: in the future, if we do actually register fields in named tuples
        //  (so their fields is not pure compiler fiction,
        //    as it is currently and in TypeScript arrays),
        //  we will want to revisit this...
      case
          (RhsBases(_, S(L(_: FunctionType)), _), _: ArrayBase)
        | (RhsBases(_, S(L(_: ArrayBase)), _), _: FunctionType)
        | (RhsBases(_, S(R(_)), _), _: FunctionType | _: ArrayBase)
        => N
    }
    def | (that: (Var, FieldType)): Opt[RhsNf] = this match {
      case RhsBot => S(RhsField(that._1, that._2))
      case RhsField(n1, t1) if n1 === that._1 => S(RhsField(n1, t1 || that._2))
      case RhsBases(p, N, trs) => S(RhsBases(p, S(R(RhsField(that._1, that._2))), trs))
      case RhsBases(p, S(R(RhsField(n1, t1))), trs) if n1 === that._1 =>
        S(RhsBases(p, S(R(RhsField(n1, t1 || that._2))), trs))
      case _: RhsField | _: RhsBases => N
    }
    def <:< (that: RhsNf): Bool = (this.toType() <:< that.toType())(Ctx.empty) // TODO less inefficient! (uncached calls to toType)
    def isBot: Bool = isInstanceOf[RhsBot.type]
  }
  case class RhsField(name: Var, ty: FieldType) extends RhsNf {
    def name_ty: Var -> FieldType = name -> ty
    override def toString: Str = s"{$name:$ty}"
  }
  case class RhsBases(
    tags: Ls[ObjectTag],
    rest: Opt[FunOrArrType \/ RhsField],
    trefs: ListSet[TypeRef]
  ) extends RhsNf {
    override def toString: Str =
      s"${tags.mkString("|")}${rest.fold("")("|" + _.fold(""+_, ""+_))}${trefs.iterator.map("|"+_).mkString}"
  }
  case object RhsBot extends RhsNf {
    override def toString: Str = "⊥"
  }
  
  
  case class Conjunct(lnf: LhsNf, vars: SortedSet[TypeVariable], rnf: RhsNf, nvars: SortedSet[TypeVariable]) extends Ordered[Conjunct] {
    def compare(that: Conjunct): Int = this.toString compare that.toString // TODO less inefficient!!
    def toType(sort: Bool = false): SimpleType =
      toTypeWith(_.toType(sort), _.toType(sort), sort)
    def toTypeWith(f: LhsNf => SimpleType, g: RhsNf => SimpleType, sort: Bool = false): SimpleType =
      ((if (sort) vars.toArray.sorted.iterator else vars.iterator) ++ Iterator(g(rnf).neg())
        ++ (if (sort) nvars.toArray.sorted.iterator else nvars).map(_.neg())).foldLeft(f(lnf))(_ & _)
    lazy val level: Int = (vars.iterator ++ nvars).map(_.level).++(Iterator(lnf.level, rnf.level)).max
    def - (fact: Factorizable): Conjunct = fact match {
      case tv: TV => Conjunct(lnf, vars - tv, rnf, nvars)
      case NegVar(tv) => Conjunct(lnf, vars, rnf, nvars - tv)
      case tt: TraitTag => lnf match {
        case LhsRefined(b, f, a, tts, rft, trs) =>
          if (tts(tt)) copy(lnf = LhsRefined(b, f, a, tts - tt, rft, trs)) else this
        case LhsTop => this
      }
      case NegTrait(tt) => rnf match {
        case RhsBases(tts, r, trs) => copy(rnf = RhsBases(tts.filterNot(_ === tt), r, trs))
        case RhsBot | _: RhsField => this
      }
    }
    def <:< (that: Conjunct): Bool =
      // trace(s"?? $this <:< $that") {
      that.vars.forall(vars) &&
        lnf <:< that.lnf &&
        that.rnf <:< rnf &&
        that.nvars.forall(nvars)
      // }(r => s"!! $r")
    def & (that: Conjunct)(implicit ctx: Ctx): Opt[Conjunct] =
      // trace(s"?? $this & $that ${lnf & that.lnf} ${rnf | that.rnf}") {
      if ((lnf.toType() <:< that.rnf.toType())(Ctx.empty)) N // TODO less inefficient! (uncached calls to toType)
      else Conjunct.mk(lnf & that.lnf getOrElse (return N), vars | that.vars
        , rnf | that.rnf getOrElse (return N)
        , nvars | that.nvars)
      // }(r => s"!! $r")
    def neg: Disjunct = Disjunct(rnf, nvars, lnf, vars)
    /** `tryMergeUnion` tries to compute the union of two conjuncts as a conjunct,
      * failing if this merging cannot be done without losing information.
      * This ends up simplifying away things like:
      *   {x: int} | {y: int} ~> anything
      *   (A -> B) | {x: C}   ~> anything  */
    def tryMergeUnion(that: Conjunct)(implicit ctx: Ctx): Opt[Conjunct] = (this, that) match {
      case _ if this <:< that => S(that)
      case _ if that <:< this => S(this)
      
      case (Conjunct(LhsTop, vs1, r1, nvs1), Conjunct(LhsTop, vs2, r2, nvs2))
        if vs1 === vs2 && nvs1 === nvs2
      =>
        S(Conjunct(LhsTop, vs1, r1 tryMergeInter r2 getOrElse (return N), nvs1))
        // * Conceptually, `tryMergeInter` could return None either because the LhsNfs cannot be merged
        // *  or because merging them would return bottom... but conjuncts cannot represent bottom.
      
      // Example:
      //    Why is it sound to merge (A -> B) & {R} | (C -> D) & {S}
      //    into ((A & C) -> (B | D)) & ({R} | {S}) ?
      //  Because the former can be distributed to
      //    (A -> B | C -> D) & (A -> B | {S}) & ({R} | C -> D) & ({R} | {S})
      //    == ((A & C) -> (B | D)) & Top & Top & ({R} | {S})
      case (Conjunct(LhsRefined(bse1, ft1, at1, ts1, rcd1, trs1), vs1, r1, nvs1)
          , Conjunct(LhsRefined(bse2, ft2, at2, ts2, rcd2, trs2), vs2, r2, nvs2))
        if bse1 === bse2 && ts1 === ts2 && vs1 === vs2 && r1 === r2 && nvs1 === nvs2
        && trs1 === trs2 // TODO could do better
      =>
        // val sameTrs = trs1 === trs2
        val sameTrs = true
        val ft = if (ft1 === ft2) ft1 else if (sameTrs) for {
            FunctionType(lhs1, rhs1) <- ft1
            FunctionType(lhs2, rhs2) <- ft2
          } yield FunctionType(lhs1 & lhs2, rhs1 | rhs2)(noProv) else return N
        val at = if (at1 === at2) at1 else
          if (sameTrs) for { at1 <- at1; at2 <- at2 } yield (at1, at2) match {
            case (tup1 @ TupleType(fs1), tup2 @ TupleType(fs2)) =>
              if (fs1.size =/= fs2.size) ArrayType(tup1.inner | tup2.inner)(noProv)
              else TupleType(tupleUnion(fs1, fs2))(noProv)
            case (tup @ TupleType(fs), ArrayType(ar)) => ArrayType(tup.inner | ar)(noProv)
            case (ArrayType(ar), tup @ TupleType(fs)) => ArrayType(tup.inner | ar)(noProv)
            case (ArrayType(ar1), ArrayType(ar2))     => ArrayType(ar1 | ar2)(noProv)
          } else return N
        val trs = if (sameTrs) trs1 else mergeTypeRefs(true, trs1, trs2)
        val rcd = RecordType(recordUnion(rcd1.fields, rcd2.fields))(noProv)
        S(Conjunct(LhsRefined(bse1, ft, at, ts1, rcd, trs), vs1, r1, nvs1))
      
      case _ => N
    }
    override def toString: Str =
      (Iterator(lnf).filter(_ =/= LhsTop) ++ vars
        ++ (Iterator(rnf).filter(_ =/= RhsBot) ++ nvars).map("~("+_+")")).mkString("∧")
  }
  
  object Conjunct {
    def of(tvs: SortedSet[TypeVariable]): Conjunct = Conjunct(LhsTop, tvs, RhsBot, ssEmp)
    def mk(lnf: LhsNf, vars: SortedSet[TypeVariable], rnf: RhsNf, nvars: SortedSet[TypeVariable])
          (implicit ctx: Ctx): Opt[Conjunct] = {
      if ((lnf, rnf) match {
        case (LhsRefined(cls, _, _, _, _, trs1), RhsBases(ts, _, trs2)) =>
          val allClasses: Ite[Str] =
            (trs1.iterator.map(_.defn) ++ trs1.iterator.flatMap(tn => ctx.allBaseClassesOf(tn.defn.name))).map(_.name) ++
              cls.iterator.flatMap(c =>
                c.parents.iterator.map(_.name) ++ (c.id match { case Var(nme) => S(nme); case _ => N }))
          allClasses.exists(clsNme => ts.exists(_.id.idStr === clsNme))
        case _ => false
      }) N
      else S(Conjunct(lnf, vars, rnf match {
        case RhsField(name, ty) => RhsField(name, ty)
        case RhsBases(prims, bf, trs) =>
          RhsBases(prims.filter(lnf & _ pipe (_.isDefined)), bf.filter {
            case L(b) => lnf & b pipe (_.isDefined)
            case R(r) => true
          }, trs)
        case RhsBot => RhsBot
      }, nvars))
    }
  }
  
  
  case class Disjunct(rnf: RhsNf, vars: SortedSet[TypeVariable], lnf: LhsNf, nvars: SortedSet[TypeVariable]) {
    def neg: Conjunct = Conjunct(lnf, nvars, rnf, vars)
    def | (that: Disjunct)(implicit ctx: Ctx): Opt[Disjunct] =
      S(Disjunct(rnf | that.rnf getOrElse (return N), vars | that.vars,
        lnf & that.lnf getOrElse (return N), nvars | that.nvars))
    override def toString: Str =
      (Iterator(rnf).filter(_ =/= RhsBot) ++ vars
        ++ (Iterator(lnf).filter(_ =/= LhsTop) ++ nvars).map("~"+_)).mkString("∨")
  }
  
  object Disjunct {
    def of(tvs: SortedSet[TypeVariable]): Disjunct = Disjunct(RhsBot, tvs, LhsTop, ssEmp)
  }
  
  
  case class DNF(cs: Ls[Conjunct]) {
    def isBot: Bool = cs.isEmpty
    def toType(sort: Bool = false): SimpleType = (if (sort) cs.sorted else cs) match {
      case Nil => BotType
      case t :: ts => t.toType(sort) | DNF(ts).toType(sort)
    }
    def level: Int = cs.maxByOption(_.level).fold(0)(_.level)
    def & (that: DNF)(implicit ctx: Ctx): DNF =
      that.cs.map(this & _).foldLeft(DNF.extr(false))(_ | _)
    def | (that: DNF)(implicit ctx: Ctx): DNF = that.cs.foldLeft(this)(_ | _)
    def & (that: Conjunct)(implicit ctx: Ctx): DNF =
      DNF(cs.flatMap(_ & that)) // Could use further simplif afterward
    def | (that: Conjunct)(implicit ctx: Ctx): DNF = {
      def go(cs: Ls[Conjunct], acc: Ls[Conjunct], toMerge: Conjunct): Ls[Conjunct] = 
        // trace(s"go?? $cs $acc M $toMerge") {
        cs match {
        case c :: cs =>
          if (c <:< toMerge) acc.reverse ::: toMerge :: cs
          else if (toMerge <:< c) acc.reverse ::: c :: cs
          else c.tryMergeUnion(toMerge) match {
            case Some(value) => acc.reverse ::: value :: cs
            case None => go(cs, c :: acc, toMerge)
          }
        case Nil => (toMerge :: acc).reverse
      }
      // }(r => s"go!! $r")
      DNF(go(cs, Nil, that))
    }
    override def toString: Str = s"DNF(${cs.mkString(" | ")})"
  }
  
  object DNF {
    def of(lnf: LhsNf): DNF = DNF(Conjunct(lnf, ssEmp, RhsBot, ssEmp) :: Nil)
    def extr(pol: Bool): DNF = if (pol) of(LhsTop) else DNF(Nil)
    def merge(pol: Bool)(l: DNF, r: DNF)(implicit ctx: Ctx): DNF = if (pol) l | r else l & r
    
    def mkDeep(ty: SimpleType, pol: Bool)
          (implicit ctx: Ctx, ptr: PreserveTypeRefs = false): DNF = {
      mk(mkDeepST(ty, pol), pol)
    }
    def mkDeepST(ty: SimpleType, pol: Bool)
          (implicit ctx: Ctx, ptr: PreserveTypeRefs = false): ST =
        // trace(s"deepDNF[$pol,$ptr,$etf](${ty})") {
        ty match {
      case ProvType(und) =>
        mkDeepST(und, pol).withProv(ty.prov)
      case TypeRange(lb, ub) => mkDeepST(if (pol) ub else lb, pol).withProv(ty.prov)
      case _ =>
        val dnf = mk(ty, pol)
        def go(polo: Opt[Bool], st: ST): ST = polo match {
          case _ if st === ty => ty.mapPol(polo)(go)
          case S(pol) => mkDeepST(st, pol)(ctx, ptr = true)
          case N => TypeRange.mk(
            mkDeepST(st, false)(ctx, ptr = true),
            mkDeepST(st, true)(ctx, ptr = true))
        }
        dnf.toType().mapPol(S(pol))(go)
    }
    // }(r => s"= $r")
    
    def mk(ty: SimpleType, pol: Bool)(implicit ctx: Ctx, ptr: PreserveTypeRefs = false): DNF =
        // trace(s"DNF[$pol,$ptr,$etf](${ty})") {
        ty match {
      case ft: FunctionType =>
        DNF.of(LhsRefined(N, S(ft), N, ssEmp, RecordType.empty, lsEmp))
      case at: ArrayBase =>
        DNF.of(LhsRefined(N, N, S(at), ssEmp, RecordType.empty, lsEmp))
      case bt: ClassTag =>
        DNF.of(LhsRefined(S(bt), N, N, ssEmp, RecordType.empty, lsEmp))
      case tt: TraitTag =>
        DNF.of(LhsRefined(N, N, N, SortedSet.single(tt), RecordType.empty, lsEmp))
      case rcd: RecordType => DNF.of(LhsRefined(N, N, N, ssEmp, rcd, lsEmp))
      case ExtrType(pol) => extr(!pol)
      case ty @ ComposedType(p, l, r) => merge(p)(mk(l, pol), mk(r, pol))
      case NegType(und) => DNF(CNF.mk(und, !pol).ds.map(_.neg))
      case tv: TypeVariable => DNF(Conjunct.of(SortedSet.single(tv)) :: Nil)
      case ProxyType(underlying) => mk(underlying, pol)
      case tr @ TypeRef(defn, targs) =>
        // * Ugly special case for primitiveTypes but we should generalize TypeRef-based simplif. instead
        if (preserveTypeRefs && !primitiveTypes.contains(defn.name)) {
          of(LhsRefined(tr.mkTag, N, N, ssEmp, RecordType.empty, ListSet.single(tr)))
        } else mk(tr.expand, pol)
      case TypeRange(lb, ub) => mk(if (pol) ub else lb, pol)
    }
    // }(r => s"= $r")
  }
  
  
  case class CNF(ds: Ls[Disjunct]) {
    def & (that: CNF): CNF = that.ds.foldLeft(this)(_ & _)
    def | (that: CNF)(implicit ctx: Ctx): CNF = that.ds.map(this | _).foldLeft(CNF.extr(false))(_ & _)
    def & (that: Disjunct): CNF =
      // Could try to merge it with the others if possible
      CNF(that :: ds)
    def | (that: Disjunct)(implicit ctx: Ctx): CNF = CNF(ds.flatMap(_ | that))
    override def toString: Str = s"CNF(${ds.mkString(" & ")})"
  }
  
  object CNF {
    def of(rnf: RhsNf): CNF = CNF(Disjunct(rnf, ssEmp, LhsTop, ssEmp) :: Nil)
    def extr(pol: Bool): CNF = if (pol) CNF(Nil) else of(RhsBot)
    def merge(pol: Bool)(l: CNF, r: CNF)(implicit ctx: Ctx): CNF = if (pol) l | r else l & r
    def mk(ty: SimpleType, pol: Bool)(implicit ctx: Ctx, ptr: PreserveTypeRefs): CNF =
      // trace(s"?CNF $ty") {
      ty match {
        case bt: BasicType => CNF.of(RhsBot | bt getOrElse (return CNF.extr(true)))
        case rcd: RecordType => CNF(rcd.fields.iterator.map(f =>
          Disjunct(RhsField(f._1, f._2), ssEmp, LhsTop, ssEmp)).toList)
        case ExtrType(pol) => extr(!pol)
        case ty @ ComposedType(p, l, r) => merge(p)(mk(l, pol), mk(r, pol))
        case NegType(und) => CNF(DNF.mk(und, !pol).cs.map(_.neg))
        case tv: TypeVariable => CNF(Disjunct.of(SortedSet.single(tv)) :: Nil)
        case ProxyType(underlying) => mk(underlying, pol)
        case tr @ TypeRef(defn, targs) =>
          if (preserveTypeRefs && !primitiveTypes.contains(defn.name)) {
            CNF(Disjunct(RhsBases(Nil, N, ListSet.single(tr)), ssEmp, LhsTop, ssEmp) :: Nil)
          } else mk(tr.expand, pol)
        case TypeRange(lb, ub) => mk(if (pol) ub else lb, pol)
      }
      // }(r => s"!CNF $r")
  }
  
  
}
