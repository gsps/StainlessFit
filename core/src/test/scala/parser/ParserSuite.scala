package stainlessfit

import org.scalatest.FunSuite
import core.parser._

class ParserSuite extends FunSuite {
  val parser = new ScalaParser(partial = false)

  // test("parser is LL1") {
  //   assert(parser.expr.isLL1)
  // }
}
