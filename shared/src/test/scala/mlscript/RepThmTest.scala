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
    
    val binops = Ls[(ST, ST) => ST](
      _ & _,
      _ | _
    )
    val unops = Ls[ST => ST](
      _.neg()
    )
    
    val dnfs = MutSet.from[ST](init)
    
    var count = 0
    var its = 0
    
    def subtypes(d: ST, e: ST): Bool = {
      constrain(d, e)(_ => return false, NoProv, ctx)
      true
    }
    
    def addDNF(d: ST): Unit = {
      if (!dnfs.exists { e =>
        subtypes(d, e) && subtypes(e, d)
      }) dnfs += d
    }
    
    while (count =/= dnfs.size) {
      count = dnfs.size
      val tmp = dnfs.toSet
      for { f <- binops; x <- tmp; y <- tmp } addDNF(f(x, y))
      for { f <- unops; x <- tmp } addDNF(f(x))
      println(dnfs.size)
    }
    dnfs.foreach(println)
    println(s"No. of unique DNFs: ${dnfs.size}")
  }
}
