import JuliaLean.Sockets.Props

/-! Refutations of the Sockets properties, each from a concrete counterexample
checked by `decide`. -/

namespace JuliaLean.Sockets

open JuliaLean

theorem ipv6Nonempty_refuted : ¬ IPv6Nonempty := by
  intro h
  exact absurd rfl (h [] (by decide))

theorem ipv6ColonPaired_refuted : ¬ IPv6ColonPaired := by
  intro h
  exact absurd (h ":1".toList (by decide)) (by decide)

theorem ipv6OneElision_refuted : ¬ IPv6OneElision := by
  intro h
  exact absurd (h "1::2::3".toList (by decide)) (by decide)

theorem ipv6ErrorIsArgument_refuted : ¬ IPv6ErrorIsArgument := by
  intro h
  exact absurd
    (h "::-1".toList (.inexactError "UInt128") rfl)
    (by decide)

theorem ipv6FieldRange_refuted : ¬ IPv6FieldRange := by
  intro h
  have hh := (h "::10000".toList (by decide)) "10000".toList (by decide) (by decide) (by decide)
  exact absurd hh.2 (by decide)

theorem ipv6FieldBare_refuted : ¬ IPv6FieldBare := by
  intro h
  exact absurd
    (h "::+1".toList (by decide) "+1".toList (by decide) (by decide) (by decide))
    (by decide)

theorem ipv4FieldBare_refuted : ¬ IPv4FieldBare := by
  intro h
  exact absurd (h "1.2.3.+4".toList (by decide) "+4".toList (by decide)) (by decide)

theorem ipv4ErrorIsArgument_refuted : ¬ IPv4ErrorIsArgument := by
  intro h
  exact absurd
    (h "1.2.3.999999999999999999999999".toList (.overflowError "overflow parsing") rfl)
    (by decide)

theorem ipv6AcceptsFiveGroupsV4_refuted : ¬ IPv6AcceptsFiveGroupsV4 := by
  intro h
  exact absurd
    (h 1 2 3 4 5 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)) (by decide)

end JuliaLean.Sockets
