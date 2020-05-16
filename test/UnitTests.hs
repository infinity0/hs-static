import           Test.Tasty

import           Control.Static.UnitTests (tests)

main :: IO ()
main = do
  defaultMain $ testGroup "Static *" [Control.Static.UnitTests.tests]
