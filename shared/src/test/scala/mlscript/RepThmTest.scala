package mlscript

import scala.collection.immutable.Set
import scala.collection.mutable.{Set => MutSet}
import mlscript.utils._, shorthands._

class RepThmTest
  extends org.scalatest.funsuite.AnyFunSuite
{
  test("representation theorem") {
    val typer = new Typer(dbg = false, verbose = false, explainErrors = false)
    import typer.{TypeDef => _, println => _, _}
    
    val typeDefs = Ls(
      TypeDef(Cls, TypeName("A"), Nil, Top),
      TypeDef(Cls, TypeName("B"), Nil, TypeName("A")),
      TypeDef(Cls, TypeName("C"), Nil, Top),
    )
    implicit val ctx: Ctx = processTypeDefs(typeDefs)(Ctx.init, println(_))
    implicit val expandTupleFields: ExpandTupleFields = false
    
    val top = ExtrType(false)(noProv)
    val bot = ExtrType(true)(noProv)
    val init = Ls(
      top,
      bot,
      RecordType(Ls(Var("x") -> FieldType(bot, top)(noProv)))(noProv),
      RecordType(Ls(Var("x") -> FieldType(bot, bot)(noProv)))(noProv),
      // RecordType(Ls(Var("y") -> FieldType(bot, top)(noProv)))(noProv),
      // RecordType(Ls(Var("y") -> FieldType(bot, bot)(noProv)))(noProv),
      FunctionType(top, top)(noProv),
      FunctionType(top, bot)(noProv),
      FunctionType(bot, top)(noProv),
      FunctionType(bot, bot)(noProv),
    ) // ::: typeDefs.map(td => clsNameToNomTag(ctx.tyDefs(td.nme.name))(noProv, ctx))
    val binops = Ls(
      // (_: DNF) & (_: DNF),
      // (_: DNF) | (_: DNF),
      (dnf1: DNF, dnf2: DNF) => DNF.mk(ComposedType(true, dnf1.toType(), dnf2.toType())(noProv), true),
      (dnf1: DNF, dnf2: DNF) => DNF.mk(ComposedType(false, dnf1.toType(), dnf2.toType())(noProv), true),
    )
    val unops = Ls(
      (dnf: DNF) => DNF.mk(NegType(dnf.toType())(noProv), true),
    )

    val dnfs = MutSet.from(init.map(DNF.mk(_, true)))
    var count = 0
    var its = 0
    while (count =/= dnfs.size) {
      count = dnfs.size
      val tmp = dnfs.toSet
      // binops.foreach(f => dnfs ++= (for { x <- tmp; y <- tmp } yield f(x, y)))
      // unops.foreach(f => dnfs ++= tmp.map(f))
      for { f <- binops; x <- tmp; y <- tmp } dnfs += f(x, y)
      for { f <- unops; x <- tmp } dnfs += f(x)
      println(dnfs.size)
    }
    dnfs.foreach(println)
    println(s"No. of unique DNFs: ${dnfs.size}")
  }
}
