import Utils._
import org.scalatest.FunSuite

import core.Core

class PartialFileSuite extends FunSuite {

  val rc = core.util.RunContext.testContext

  for (f <- files("examples/partial", _.endsWith("sf"))) {
    test(s"Type checking file $f with partial translation") {
      val result = Core.typeCheckFile(rc, f, false, partialize = true)
      assert(result.isRight)
      val Right((success, _)) = result
      assert(success)
    }
  }
}
