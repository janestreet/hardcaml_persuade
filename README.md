# Hardcaml_persaude

`Hardcaml_persaude` is a library to express formal properties for hardware designs that
compile into SVA and LTL properties. Similar to SVA, the library has a notion of constructs
that are only valid for properties (eg: always) and those that are valid in sequences and properties.

An example of property in `Hardcaml_persaude` can look like:

```
let a : Signal.t = ... in
let b : Signal.t = ... in
[ p a; delay 1; p b ] |-> g (p c)
```

which loosely translates to a seuence of a asserted followed by b asserting in a clock
cycle, c must always hold true forever.

The main way you should specify Hardcaml_persaude propertie is using the ppx. The ppx automatically opens
`Hardcaml_persaude` in your local scope:

```
let%hw_persuade name_of_my_new_property =
  Assert, [ p a; delay 1; p b ] |-> g (p c)
in
```

`Hardcaml_persuade` rejects ill-defined properties at build time, some examples include:

```
concat [ p a; delay 1 ] -- dangling delay doesn't semantically mean anything
concat [ delay_at_least 1; delay_at_most 5 ] -- combining >= 1 and <= 5 delay back to back is ill-defined
```

