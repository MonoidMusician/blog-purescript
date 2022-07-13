{-
Welcome to a Spago project!
You can edit this file as you like.

Need help? See the following resources:
- Spago documentation: https://github.com/purescript/spago
- Dhall language tour: https://docs.dhall-lang.org/tutorials/Language-Tour.html

When creating a new Spago project, you can use
`spago init --no-comments` or `spago init -C`
to generate this file without the comments in this block.
-}
{ name = "my-project"
, dependencies =
  [ "aff"
  , "argonaut"
  , "arrays"
  , "avar"
  , "behaviors"
  , "bifunctors"
  , "bolson"
  , "console"
  , "control"
  , "datetime"
  , "debug"
  , "deku"
  , "effect"
  , "either"
  , "enums"
  , "event"
  , "filterable"
  , "foldable-traversable"
  , "foreign"
  , "free"
  , "gen"
  , "integers"
  , "js-uri"
  , "lcg"
  , "lists"
  , "maybe"
  , "newtype"
  , "nonempty"
  , "now"
  , "numbers"
  , "ordered-collections"
  , "partial"
  , "prelude"
  , "profunctor"
  , "psci-support"
  , "quickcheck"
  , "refs"
  , "st"
  , "strings"
  , "transformers"
  , "tuples"
  , "type-equality"
  , "typelevel"
  , "unsafe-coerce"
  , "variant"
  , "web-events"
  , "web-html"
  , "web-uievents"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
}
