package mlscript

import scala.util.chaining._
import scala.collection.mutable
import fastparse._, fastparse.ScalaWhitespace._
import mlscript.utils._, shorthands._
import mlscript.Lexer._

/** Parser for an ML-style input syntax, used in the legacy `ML*` tests. */
@SuppressWarnings(Array("org.wartremover.warts.All"))
class MLParser(origin: Origin, indent: Int = 0, recordLocations: Bool = true) {
  
  val keywords = Set(
    "def", "class", "trait", "type", "method", "mut",
    "let", "rec", "in", "fun", "with", "undefined", "null",
    "if", "then", "else", "match", "case", "of")
  def kw[p: P](s: String) = s ~~ !(letter | digit | "_" | "'")
  
  // NOTE: due to bug in fastparse, the parameter should be by-name!
  def locate[p:P, L <: Located](tree: => P[L]): P[L] = (Index ~~ tree ~~ Index).map {
    case (i0, n, i1) => n.withLoc(i0, i1, origin)
  }
  
  def toParams(t: Term): Tup = t match {
    case t: Tup => t
    case _ => Tup((N, t) :: Nil)
  }
  def toParamsTy(t: Type): Tuple = t match {
    case t: Tuple => t
    case _ => Tuple((N, t) :: Nil)
  }
  
  def letter[p: P]     = P( lowercase | uppercase )
  def lowercase[p: P]  = P( CharIn("a-z") )
  def uppercase[p: P]  = P( CharIn("A-Z") )
  def digit[p: P]      = P( CharIn("0-9") )
  def number[p: P]: P[Int] = P( CharIn("0-9").repX(1).!.map(_.toInt) )
  def ident[p: P]: P[String] =
    P( (letter | "_") ~~ (letter | digit | "_" | "'").repX ).!.filter(!keywords(_))
  
  def termOrAssign[p: P]: P[Statement] = P( term ~ ("=" ~ term).? ).map {
    case (expr, N) => expr
    case (pat, S(bod)) => LetS(false, pat, bod)
  }

  def term[p: P]: P[Term] = P(let | fun | ite | withsAsc | _match)

  def lit[p: P]: P[Lit] =
    locate(number.map(x => IntLit(BigInt(x))) | Lexer.stringliteral.map(StrLit(_))
    | P(kw("undefined")).map(x => UnitLit(true)) | P(kw("null")).map(x => UnitLit(false)))
  
  def variable[p: P]: P[Var] = locate(ident.map(Var))
  
  def parens[p: P]: P[Term] = locate(P( "(" ~/ term.rep(0, ",") ~ ",".!.? ~ ")" ).map {
    case (Seq(t), N) => t
    case (Seq(t), N) => Tup(N -> t :: Nil)
    case (ts, _) => Tup(ts.iterator.map(f => N -> f).toList)
  })
  
  def tup[p: P]: P[Tup] = locate(P( "(" ~/ term.rep(0, ",") ~ ",".!.? ~ ")" ).map {
    case (Seq(t), N) => Tup(N -> t :: Nil)
    case (ts, _) => Tup(ts.iterator.map(f => N -> f).toList)
  } | subterm.map(t => Tup(N -> t :: Nil)))

  def subtermNoSel[p: P]: P[Term] = P( parens | record | lit | variable )
  
  def subterm[p: P]: P[Term] = P( Index ~~ subtermNoSel ~ (
    // Fields:
    ("." ~/ (variable |
      locate(("(" ~/ ident ~ "." ~ ident ~ ")")
        .map {case (prt, id) => Var(s"${prt}.${id}")}))
    ).map {(t: Var) => Left(t)} |
    // Array subscripts:
    ("[" ~ term ~/ "]" ~~ Index).map {Right(_)}
    // Assignment:
    ).rep).map {
      case (i0, st, sels) =>
        sels.foldLeft(st)((acc, t) => t match {
          case Left(se) => Sel(acc, se)
          case Right((su, i1)) => Subs(acc, su).withLoc(i0, i1, origin)
        })
    }

  def record[p: P]: P[Rcd] = locate(P(
      "{" ~/ (variable ~ "=" ~ term map L.apply).|(variable map R.apply).rep(sep = ";") ~ "}"
    ).map { fs => Rcd(fs.map{ 
        case L((v, t)) => v -> t
        case R(id) => id -> id }.toList)})
  
  def fun[p: P]: P[Term] = locate(P( kw("fun") ~/ tup ~ "->" ~ term ).map(nb => Lam(nb._1, nb._2)))
  
  def let[p: P]: P[Term] = locate(P(
      kw("let") ~/ kw("rec").!.?.map(_.isDefined) ~ variable ~ tup.rep ~ "=" ~ term ~ kw("in") ~ term
    ) map {
      case (rec, id, ps, rhs, bod) => Let(rec, id, ps.foldRight(rhs)((i, acc) => Lam(i, acc)), bod)
    })
  
  def ite[p: P]: P[Term] = P( kw("if") ~/ term ~ kw("then") ~ term ~ kw("else") ~ term ).map(ite =>
    App(App(App(Var("if"), ite._1), ite._2), ite._3))
  
  def withsAsc[p: P]: P[Term] = P( binops ~ (":" ~/ ty).rep ).map {
    case (withs, ascs) => ascs.foldLeft(withs)(Asc)
  }
  
  def apps[p: P]: P[Term] = P( (subterm | tup) ~ tup.rep ).map {
    case (prefix, argLists) => argLists.foldLeft(prefix)(App)
  }
  
  def _match[p: P]: P[CaseOf] =
    locate(P( kw("case") ~/ term ~ "of" ~ ("{" ~ "|".? ~ matchArms("|") ~ "}" | matchArms(",")) ).map(CaseOf.tupled))
  def matchArms[p: P](sep: Str): P[CaseBranches] = P(
    ( ("_" ~ "->" ~ term).map(Wildcard)
    | ((lit | variable) ~ "->" ~ term ~ matchArms2(sep))
      .map { case (t, b, rest) => Case(t, b, rest) }
    ).?.map {
      case None => NoCases
      case Some(b) => b
    }
  )
  def matchArms2[p: P](sep: Str): P[CaseBranches] = (sep ~ matchArms(sep)).?.map(_.getOrElse(NoCases))
  
  private val prec: Map[Char,Int] = List(
    ":",
    "|",
    "^",
    "&",
    "= !",
    "< >",
    "+ -",
    "* / %",
    ".",
  ).zipWithIndex.flatMap {
    case (cs,i) => cs.filterNot(_ == ' ').map(_ -> i)
  }.toMap.withDefaultValue(Int.MaxValue)
  def precedence(op: String): Int = prec(op.head) min prec(op.last)
  
  // Adapted from: https://github.com/databricks/sjsonnet/blob/master/sjsonnet/src/sjsonnet/Parser.scala#L136-L180
  def binops[p: P]: P[Term] =
    P(apps ~ (Index ~~ operator.! ~~ Index ~/ apps).rep ~ "").map { case (pre, fs) =>
      var remaining = fs
      def climb(minPrec: Int, current: Term): Term = {
        var result = current
        while (
          remaining.headOption match {
            case None => false
            case Some((off0, op, off1, next)) =>
              val prec: Int = precedence(op)
              if (prec < minPrec) false
              else {
                remaining = remaining.tail
                val rhs = climb(prec + 1, next)
                result = App(App(Var(op).withLoc(off0, off1, origin), toParams(result)), toParams(rhs))
                true
              }
          }
        )()
        result
      }
      climb(0, pre)
    }
  def operator[p: P]: P[Unit] = P(
    !symbolicKeywords ~~ (!StringIn("/*", "//") ~~ (CharsWhile(OpCharNotSlash) | "/")).rep(1)
  ).opaque("operator")
  def symbolicKeywords[p: P] = P{
    StringIn(
      "|",
      "~",
      ";", "=>", "=", "->", "<-",
      ":",
      "#", "@", "\\", "\u21d2", "\u2190"
    ) ~~ !OpChar
  }.opaque("symbolic keywords")
  
  def expr[p: P]: P[Term] = P( term ~ End )
  
  def defDecl[p: P]: P[Def] =
    locate(P((kw("def") ~ variable ~ tyParams ~ ":" ~/ ty map {
      case (id, tps, t) => Def(true, id, R(PolyType(tps, t)))
    }) | (kw("rec").!.?.map(_.isDefined) ~ kw("def") ~/ variable ~ tup.rep ~ "=" ~ term map {
      case (rec, id, ps, bod) => Def(rec, id, L(ps.foldRight(bod)((i, acc) => Lam(i, acc))))
    })))
  
  def tyKind[p: P]: P[TypeDefKind] = (kw("class") | kw("trait") | kw("type")).! map {
    case "class" => Cls
    case "trait" => Trt
    case "type"  => Als
  }
  def tyDecl[p: P]: P[TypeDef] =
    P((tyKind ~/ tyName ~ tyParams).flatMap {
      case (k @ (Cls | Trt), id, ts) => (":" ~ ty).? ~ (mthDecl(id) | mthDef(id)).rep.map(_.toList) map {
        case (bod, ms) => TypeDef(k, id, ts, bod.getOrElse(Top), 
          ms.collect { case R(md) => md }, ms.collect{ case L(md) => md })
      }
      case (k @ Als, id, ts) => "=" ~ ty map (bod => TypeDef(k, id, ts, bod))
    })
  def tyParams[p: P]: P[Ls[TypeName]] =
    ("[" ~ tyName.rep(0, ",") ~ "]").?.map(_.toList.flatten)
  def mthDecl[p: P](prt: TypeName): P[R[MethodDef[Right[Term, Type]]]] = 
    P(kw("method") ~ variable ~ tyParams ~ ":" ~/ ty map {
      case (id, ts, t) => R(MethodDef[Right[Term, Type]](true, prt, id, ts, R(t)))
    })
  def mthDef[p: P](prt: TypeName): P[L[MethodDef[Left[Term, Type]]]] = 
    P(kw("rec").!.?.map(_.isDefined) ~ kw("method") ~ variable ~ tyParams ~ tup.rep ~ "=" ~/ term map {
      case (rec, id, ts, ps, bod) =>
        L(MethodDef(rec, prt, id, ts, L(ps.foldRight(bod)((i, acc) => Lam(i, acc)))))
    })
  
  def ty[p: P]: P[Type] = P( tyNoAs ~ ("as" ~ tyVar).rep ).map {
    case (ty, ass) => ass.foldLeft(ty)((a, b) => Recursive(b, a))
  }
  def tyNoAs[p: P]: P[Type] = P( tyNoUnion.rep(1, "|") ).map(_.reduce(Union))
  def tyNoUnion[p: P]: P[Type] = P( tyNoInter.rep(1, "&") ).map(_.reduce(Inter))
  def tyNoInter[p: P]: P[Type] = P( tyNoFun ~ ("->" ~/ tyNoInter).? ).map {
    case (l, S(r)) => Function(toParamsTy(l), r)
    case (l, N) => l
  }
  // Note: field removal types are not supposed to be explicitly used by programmers,
  //    and they won't work in negative positions,
  //    but parsing them is useful in tests (such as shared/src/test/diff/mlscript/Annoying.mls)
  def tyNoFun[p: P]: P[Type] = P( (rcd | ctor | parTy) )
  def ctor[p: P]: P[Type] = locate(P( tyName ~ "[" ~ ty.rep(0, ",") ~ "]" ) map {
    case (tname, targs) => AppliedType(tname, targs.toList)
  }) | tyNeg | tyName | tyTag | tyVar | tyWild | litTy
  def tyNeg[p: P]: P[Type] = locate(P("~" ~/ tyNoFun map { t => Neg(t) }))
  def tyTag[p: P]: P[TypeTag] = locate(P("#" ~~ (ident map TypeTag)))
  def tyName[p: P]: P[TypeName] = locate(P(ident map TypeName))
  def tyVar[p: P]: P[TypeVar] = locate(P("'" ~ ident map (id => TypeVar(R("'" + id), N))))
  def tyWild[p: P]: P[Bounds] = locate(P("?".! map (_ => Bounds(Bot, Top))))
  def rcd[p: P]: P[Record] =
    locate(P( "{" ~/ ( variable ~ ":" ~ ty).rep(sep = ";") ~ "}" )
      .map(_.toList.map {
        case (v, t) => v -> Field(None, t)
      } pipe Record))
  def parTy[p: P]: P[Type] = locate(P( "(" ~/ ty.rep(0, ",").map(_.map(N -> _).toList) ~ ",".!.? ~ ")" ).map {
    case (N -> ty :: Nil, N) => ty
    case (fs, _) => Tuple(fs)
  })
  def litTy[p: P]: P[Type] = P( lit.map(l => Literal(l).withLocOf(l)) )
  
  def toplvl[p: P]: P[Statement] =
    P( defDecl | tyDecl | termOrAssign )
  def pgrm[p: P]: P[Pgrm] = P( (";".rep ~ toplvl ~ topLevelSep.rep).rep.map(_.toList) ~ End ).map(Pgrm)
  def topLevelSep[p: P]: P[Unit] = ";"
  
  private var curHash = 0
  def nextHash: Int = {
    val res = curHash
    curHash = res + 1
    res
  }
  
}
object MLParser {
  
  def addTopLevelSeparators(lines: IndexedSeq[Str]): IndexedSeq[Str] = {
    (lines.iterator ++ lines.lastOption).toList.sliding(2).map {
      case l0 :: l1 :: Nil =>
        if (l1.startsWith(" ") || l1.startsWith("\t")) l0 + "\n"
        else l0 + ";"
      case l :: Nil => l
      case _ => die
    }.toIndexedSeq
  }
  
}
