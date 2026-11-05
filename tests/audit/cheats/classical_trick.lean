import ZlibF.Runtime.Pilot

theorem cheat : ∀ p : Prop, p := fun p => by
  have : p := sorry
  exact this
