module Main where

import Prelude

import Deku.Toplevel (hydrate)
import Effect (Effect)
import Parser.Main as Parser

main :: Effect Unit
main = hydrate Parser.main
