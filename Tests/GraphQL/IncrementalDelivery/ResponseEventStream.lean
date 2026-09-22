import GraphQL.IncrementalDelivery.Observation

namespace GraphQL.IncrementalDelivery.Tests.ResponseEventStream
open GraphQL.IncrementalDelivery.Execution

/-- The resumable stream API is available through Observation, without Correctness. -/
example (stream : ResponseEventStream) (input : stream.Input)
    (allowed : stream.Accepts input)
    : (stream.next input allowed).1 = ((stream.mapEvent input).run stream.ids).1 :=
  rfl

/-- One accepted observation appends exactly its input to the source history. -/
example (stream : ResponseEventStream) (input : stream.Input)
    (allowed : stream.Accepts input)
    : (stream.next input allowed).2.source.history = stream.source.history ++ [input] :=
  rfl

/-- The updated cursor retains the ID state returned by the same mapper call. -/
example (stream : ResponseEventStream) (input : stream.Input)
    (allowed : stream.Accepts input)
    : (stream.next input allowed).2.ids = ((stream.mapEvent input).run stream.ids).2 :=
  rfl

end GraphQL.IncrementalDelivery.Tests.ResponseEventStream
