# Give generic certificates a codec

A certificate for a generic function needs a way to encode each type
parameter's values and decode them when a loop reads them back from the
interpreter's environment. The codec proves that decoding an encoded value
returns the original value. It also proves that the encoding is neither
`null` nor `undefined`.

The two exclusions are necessary because a generic value can occur inside
`T | null` or an optional value. Without them, an encoding of a payload could
be indistinguishable from the outer `null` or `undefined` case. The certificate
would then make a false round-trip claim. A project may choose any encoding
that proves all three laws. Tolean does not require a particular representation.

A generic interface gets an encoder and decoder that take one codec for each
type parameter. Its codec constructor uses those same laws, so a field of type
`T` keeps the representation chosen for `T`. This also covers generic
interfaces whose fields are optional or nullable. Generic interfaces that
refer to themselves remain refused, because their recursive codecs need a
separate termination argument. A generic interface use is also refused when
an argument is not a bare type parameter. Its field codecs need specialization
for those type arguments, which this step does not implement.

The certificate keeps the source function's Lean signature unchanged. It
quantifies its proof over the required codecs instead. The existing
`program_sound` theorem already covers the translated IR for generic
functions, so this change needs no new axiom or exception in that proof.

Type parameters and interfaces erase before JavaScript execution. This choice
adds no runtime feature and no edition gate. The certificate records only the
encoding and decoding laws that connect Lean values to the interpreter's
values.
