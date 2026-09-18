import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.SpecificationSource

/-! Optional finite nonblocking and its maximal relational source language.
Viability is a proof specification, not an executable policy or a selected future.
-/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Viable histories retain their initial notices and batch boundaries
-----------------------------------------------------------------------------------------

/-- A terminal extension makes its existing prefix valid. Witness: run prefix closure.
-/
theorem History.CanFinish.valid {work history} (viable : history.CanFinish work)
    : ValidHistory work history := by
  obtain ⟨suffix, run⟩ := viable
  exact ValidHistory.prefix (Or.inr run)

/-- Viability is prefix closed. Witness: prepend the discarded batches to the suffix.
-/
theorem History.CanFinish.prefix {work groups streams before after}
    (viable : (History.mk groups streams (before ++ after)).CanFinish work)
    : (History.mk groups streams before).CanFinish work := by
  obtain ⟨suffix, run⟩ := viable
  exact ⟨after ++ suffix, by simpa only [List.append_assoc] using run⟩

/-- The viable source admits exactly prefixes of terminal runs for the given notices.
It is a relational benchmark for progress policies, not an online scheduling algorithm.
-/
def viableSource (work : Work) (groups streams : List DeliveryNode) : WorkQueueResult :=
  {
    initialGroups := groups,
    initialStreams := streams,
    workEventStream :=
      {
        admissible := fun batches => (History.mk groups streams batches).CanFinish work,
        finished := fun batches => AdmissibleRun work ⟨groups, streams, batches⟩
      }
  }

/-- Viable-source continuations remain in that same source. Witness: the terminal suffix
already supplied by admission, without choosing one in the source definition.
-/
theorem viableSource_nonblocking (work groups streams)
    : (viableSource work groups streams).Nonblocking := by
  intro batches viable
  exact viable

/-- A viable initialization gives a conforming nonblocking source. Witness: prefix
closure and exact termination; a supplied possible run excludes vacuous initialization.
-/
theorem viableSource_conforms {work groups streams}
    (initial : (History.mk groups streams []).CanFinish work)
    : (viableSource work groups streams).Conforms work := by
  refine ⟨⟨rfl, initial⟩, ?_, fun _ viable => viable.valid, ?_⟩
  · intro before after earlier viable
    obtain ⟨suffix, rfl⟩ := earlier
    exact viable.prefix
  · intro batches
    constructor
    · intro run
      exact ⟨⟨[], by simpa [viableSource] using run⟩, run⟩
    · exact fun h => h.2

/-- Any conforming nonblocking source admits only viable histories. Witness: its own
finished continuation is a terminal work run, not merely an alternative-source run.
-/
theorem nonblocking_viable {work} {result : WorkQueueResult}
    (conforms : result.Conforms work)
    (nonblocking : result.Nonblocking) {batches}
    (admitted : result.workEventStream.admissible batches)
    : (result.toHistory batches).CanFinish work := by
  obtain ⟨suffix, finished⟩ := nonblocking batches admitted
  exact ⟨suffix, (conforms.2.2.2 _).mp finished |>.2⟩

/-- A nonblocking conforming source cannot have an unfinished maximal history.
Witness: its finished suffix must be empty if no strictly longer admitted history exists.
-/
theorem maximal_finished {work} {result : WorkQueueResult}
    (conforms : result.Conforms work)
    (nonblocking : result.Nonblocking) {batches}
    (admitted : result.workEventStream.admissible batches)
    (maximal
      : ∀ suffix, result.workEventStream.admissible (batches ++ suffix) → suffix = [])
    : result.workEventStream.finished batches := by
  obtain ⟨suffix, finished⟩ := nonblocking batches admitted
  have empty := maximal suffix ((conforms.2.2.2 _).mp finished).1
  simpa only [empty, List.append_nil] using finished

end GraphQL.IncrementalDelivery.WorkScheduler
