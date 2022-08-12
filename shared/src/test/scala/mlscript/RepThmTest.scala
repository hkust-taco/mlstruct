package mlscript

import scala.collection.immutable.Set
import scala.collection.mutable.{Set => MutSet, Map => MutMap}
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
    
    val eqSets: MutMap[ST, MutSet[ST]] =
      MutMap.from(init.iterator.map(ty =>
        ty -> (MutSet.empty += ty)))
    
    var count = 0
    var its = 0
    
    def subtypes(d: ST, e: ST): Bool = {
      constrain(d, e)(_ => return false, NoProv, ctx)
      true
    }
    
    def addType(_d: ST): Unit = {
      val d = DNF.mk(_d, true).toType(sort = true)
      if (!eqSets.valuesIterator.exists(_.contains(d)))
        if (!eqSets.exists { case (representative, set) =>
          subtypes(d, representative) && subtypes(representative, d) && {
            set += d
            true
          }
        }) { eqSets += (d -> (MutSet.empty[ST] += d)) }
    }
    
    while (count =/= eqSets.size) {
      // count = eqSets.size
      val tmp = eqSets.keySet
      count = tmp.size
      println(count)
      for { f <- binops; xs <- tmp; ys <- tmp } {
        // println(x,y,f(x,y))
        addType(f(xs, ys))
      }
      for { f <- unops; xs <- tmp } addType(f(xs))
    }
    val results = eqSets.keySet
    results.foreach(r => println(expandType(r).show))
    println(s"No. of unique types: ${results.size}")
  }
}
