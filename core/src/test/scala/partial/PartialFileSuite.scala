package stainlessfit

import Utils._
import org.scalatest.FunSuite

import core.{Config, Core}

class PartialFileSuite extends FunSuite {

  def checkAll(partial: Boolean) = {
    implicit val rc = {
      val config = Config.default.copy(partial = partial)
      new core.util.RunContext(config)
    }

    for (f <- files("examples/partial", _.endsWith("sf"))) {
      test(s"Type checking file $f with partial translation") {
        val result = Core.typeCheckFile(f, false)
        assert(result.isRight)
        val Right((success, _)) = result
        assert(success)
      }
    }
  }

  checkAll(partial = false)
  checkAll(partial = true)
}
