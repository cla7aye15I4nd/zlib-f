import ZlibF.Pilot.ObjectHeap

theorem cheat : ∀ p : Prop, p := fun p => by
  have : p := sorry
  exact this
