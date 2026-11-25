import Conjectures.StableKneserK3.ColoringCertificate
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace StableKneserK3

open SimpleGraph ColoringCertificate

-- Check each block before elaborating the next one to bound peak kernel memory.
set_option Elab.async false

private def unpack {n : ℕ} [NeZero n] : ℕ → ℕ → List (Fin n)
  | 0, _ => []
  | k+1, bits => Fin.ofNat n (bits % 32) :: unpack k (bits / 32)

private def decodeState {n : ℕ} [NeZero n] (used len bits : ℕ) : State (Fin n) :=
  ⟨used, go len bits⟩
where
  go : ℕ → ℕ → List (Fin n × ℕ)
    | 0, _ => []
    | k+1, b => (Fin.ofNat n (b / 8 % 32), b % 8) :: go k (b / 256)

namespace Cycle6Cert

private def adj (i j : Fin 2) : Bool :=
  (0x6 : ℕ).testBit (i.val * 2 + j.val)

private def s0 : List (State (Fin 2)) :=
  [⟨0, []⟩]

private def s1 : List (State (Fin 2)) :=
  []

private theorem step1 : Possible adj 1 s0 → Possible adj 1 s1 :=
  advance (unpack 2 0x20) (by rfl)

private theorem lower : ¬ Colorable (cycleGraph 6) 1 := by
  let S : Fin 2 → Finset (Fin 6) := fun i => #v[{0, 2, 4}, {1, 3, 5}][i]
  have hs : ∀ i, StableTriple (cycleGraph _) (S i) := by unfold StableTriple; decide +kernel
  have he : ∀ i j, adj i j → Disjoint (S i) (S j) := by decide +kernel
  rintro ⟨c, hc⟩
  have h0 : Possible adj 1 s0 := possible_start (fun i => c ⟨S i, hs i⟩)
    (fun i j hij => hc _ _ (he i j hij))
  have h1 := step1 h0
  obtain ⟨s, hs', _⟩ := h1
  cases hs'

end Cycle6Cert

theorem cycle6_tight : K3Tight (cycleGraph 6) :=
  ⟨Cycle6Cert.lower, upper_bound _ (by decide)⟩

namespace Cycle7Cert

private def adj (i j : Fin 7) : Bool :=
  (0x303038381818 : ℕ).testBit (i.val * 7 + j.val)

private def s0 : List (State (Fin 7)) :=
  [⟨0, []⟩]

private def s1 : List (State (Fin 7)) :=
  []

private theorem step1 : Possible adj 2 s0 → Possible adj 2 s1 :=
  advance (unpack 7 0x184509060) (by rfl)

private theorem lower : ¬ Colorable (cycleGraph 7) 2 := by
  let S : Fin 7 → Finset (Fin 7) := fun i => #v[{0, 2, 4}, {0, 2, 5}, {0, 3, 5}, {1, 3, 5}, {1, 3, 6}, {1, 4, 6},
    {2, 4, 6}][i]
  have hs : ∀ i, StableTriple (cycleGraph _) (S i) := by unfold StableTriple; decide +kernel
  have he : ∀ i j, adj i j → Disjoint (S i) (S j) := by decide +kernel
  rintro ⟨c, hc⟩
  have h0 : Possible adj 2 s0 := possible_start (fun i => c ⟨S i, hs i⟩)
    (fun i j hij => hc _ _ (he i j hij))
  have h1 := step1 h0
  obtain ⟨s, hs', _⟩ := h1
  cases hs'

end Cycle7Cert

theorem cycle7_tight : K3Tight (cycleGraph 7) :=
  ⟨Cycle7Cert.lower, upper_bound _ (by decide)⟩

namespace Cycle8Cert

private def adj (i j : Fin 16) : Bool :=
  (0x122502b000d889481035001ec00a102760033025c9406c0036008d40078089c0 : ℕ).testBit (i.val * 16 + j.val)

private def s0 : List (State (Fin 16)) :=
  [⟨0, []⟩]

private def s1 : List (State (Fin 16)) :=
  [decodeState 3 13 0x31102862415979084a713a68,
   decodeState 3 9 0x311028624159790a,
   decodeState 3 4 0x31102a,
   decodeState 3 3 0x3112]

private theorem step1 : Possible adj 3 s0 → Possible adj 3 s1 :=
  advance (unpack 32 0x69dc90bd683852e2354d238ed391c90a86c288c0) (by rfl)

private def s2 : List (State (Fin 16)) :=
  [decodeState 3 10 0x3112415979084a5118,
   decodeState 3 7 0x31124159790a]

private theorem step2 : Possible adj 3 s1 → Possible adj 3 s2 :=
  advance (unpack 32 0x1a9217ad0e49dc76914e391a3485eb428693a883) (by rfl)

private def s3 : List (State (Fin 16)) :=
  []

private theorem step3 : Possible adj 3 s2 → Possible adj 3 s3 :=
  advance (unpack 11 0x346a239273b88d) (by rfl)

private theorem lower : ¬ Colorable (cycleGraph 8) 3 := by
  let S : Fin 16 → Finset (Fin 8) := fun i => #v[{0, 2, 4}, {0, 2, 5}, {0, 2, 6}, {0, 3, 5}, {0, 3, 6}, {0, 4, 6},
    {1, 3, 5}, {1, 3, 6}, {1, 3, 7}, {1, 4, 6}, {1, 4, 7}, {1, 5, 7},
    {2, 4, 6}, {2, 4, 7}, {2, 5, 7}, {3, 5, 7}][i]
  have hs : ∀ i, StableTriple (cycleGraph _) (S i) := by unfold StableTriple; decide +kernel
  have he : ∀ i j, adj i j → Disjoint (S i) (S j) := by decide +kernel
  rintro ⟨c, hc⟩
  have h0 : Possible adj 3 s0 := possible_start (fun i => c ⟨S i, hs i⟩)
    (fun i j hij => hc _ _ (he i j hij))
  have h1 := step1 h0
  have h2 := step2 h1
  have h3 := step3 h2
  obtain ⟨s, hs', _⟩ := h3
  cases hs'

end Cycle8Cert

theorem cycle8_tight : K3Tight (cycleGraph 8) :=
  ⟨Cycle8Cert.lower, upper_bound _ (by decide)⟩

namespace Cycle9Cert

private def adj (i j : Fin 30) : Bool :=
  (0x120859680a2830b00c306362594085100a5d40000d9e0c025a2804021e706030b0c0c06365012800d6c03001edc9400294480027e6c0000d8d80025a02c00e3e350008707800c2e270018dc965a001b0c2c003618d00235d4000079e0002279c000e035b000c07b400c027e001c0e3c00 : ℕ).testBit (i.val * 30 + j.val)

private def s0 : List (State (Fin 30)) :=
  [⟨0, []⟩]

private def s1 : List (State (Fin 30)) :=
  [decodeState 4 15 0x5118ead161088972822bc0439aa8,
   decodeState 4 10 0x5118ead16108897283,
   decodeState 4 9 0x5118ead161088973,
   decodeState 4 8 0x5118ead161088b,
   decodeState 4 7 0x5118ead1610b,
   decodeState 4 6 0x5118ead163,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step1 : Possible adj 4 s0 → Possible adj 4 s1 :=
  advance (unpack 32 0xaccd39230bbd67c7ee6bbcea8c160e8859ae8d40) (by rfl)

private def s2 : List (State (Fin 30)) :=
  [decodeState 4 18 0x5118ead1610889728348212a7bd9c03193,
   decodeState 4 11 0x5118ead1610889728349,
   decodeState 4 9 0x5118ead161088973,
   decodeState 4 8 0x5118ead161088b,
   decodeState 4 7 0x5118ead1610b,
   decodeState 4 6 0x5118ead163,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step2 : Possible adj 4 s1 → Possible adj 4 s2 :=
  advance (unpack 32 0x91b1b7f2a8589f8b94b2361fc9ed78b96a44f1fb) (by rfl)

private def s3 : List (State (Fin 30)) :=
  [decodeState 4 18 0x5118ead1610889728349212a7bd9c03193,
   decodeState 4 9 0x5118ead161088973,
   decodeState 4 8 0x5118ead161088b,
   decodeState 4 7 0x5118ead1610b,
   decodeState 4 6 0x5118ead163,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step3 : Possible adj 4 s2 → Possible adj 4 s3 :=
  advance (unpack 32 0x91b1b7f2a8589f8b94b2361fc9af6d5e1a5a9328) (by rfl)

private def s4 : List (State (Fin 30)) :=
  [decodeState 4 16 0x5118ead161088973482031ab9228b9,
   decodeState 4 11 0x5118ead1610889734821,
   decodeState 4 10 0x5118ead16108897349,
   decodeState 4 8 0x5118ead161088b,
   decodeState 4 7 0x5118ead1610b,
   decodeState 4 6 0x5118ead163,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step4 : Possible adj 4 s3 → Possible adj 4 s4 :=
  advance (unpack 32 0xb965c7a30dddcb2acea5bad772f1fbaa30622788) (by rfl)

private def s5 : List (State (Fin 30)) :=
  [decodeState 4 16 0x5118ead161088973482131b97ad9c0,
   decodeState 4 14 0x5118ead161088973482131b97b,
   decodeState 4 10 0x5118ead16108897349,
   decodeState 4 8 0x5118ead161088b,
   decodeState 4 7 0x5118ead1610b,
   decodeState 4 6 0x5118ead163,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step5 : Possible adj 4 s4 → Possible adj 4 s5 :=
  advance (unpack 32 0xc6df94637593f28c6cf593cb7e550bb95f832f0d) (by rfl)

private def s6 : List (State (Fin 30)) :=
  [decodeState 4 18 0x5118ead161088973492031aa6b9328b9d9,
   decodeState 4 13 0x5118ead161088973492031ab,
   decodeState 4 11 0x5118ead1610889734921,
   decodeState 4 8 0x5118ead161088b,
   decodeState 4 7 0x5118ead1610b,
   decodeState 4 6 0x5118ead163,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step6 : Possible adj 4 s5 → Possible adj 4 s6 :=
  advance (unpack 32 0xddcb26d78fdb6a85e0c4c2da592ea5c233cca245) (by rfl)

private def s7 : List (State (Fin 30)) :=
  [decodeState 4 16 0x5118ead161088973492131b82b7a92,
   decodeState 4 13 0x5118ead161088973492131b9,
   decodeState 4 8 0x5118ead161088b,
   decodeState 4 7 0x5118ead1610b,
   decodeState 4 6 0x5118ead163,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step7 : Possible adj 4 s6 → Possible adj 4 s7 :=
  advance (unpack 32 0x93f88c6da7ac9e5bf2a85dcafc1978b964de3d18) (by rfl)

private def s8 : List (State (Fin 30)) :=
  [decodeState 4 17 0x5118ead161088b72821028c3b259bb9a,
   decodeState 4 12 0x5118ead161088b72821029,
   decodeState 4 10 0x5118ead161088b7283,
   decodeState 4 9 0x5118ead161088b73,
   decodeState 4 7 0x5118ead1610b,
   decodeState 4 6 0x5118ead163,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step8 : Possible adj 4 s7 → Possible adj 4 s8 :=
  advance (unpack 32 0x9dd76c14507616d2c9752e11ce2245c6dfc46375) (by rfl)

private def s9 : List (State (Fin 30)) :=
  [decodeState 4 18 0x5118ead161088b728348a2b2ca40c37928,
   decodeState 4 15 0x5118ead161088b728348a2b2ca43,
   decodeState 4 11 0x5118ead161088b728349,
   decodeState 4 9 0x5118ead161088b73,
   decodeState 4 7 0x5118ead1610b,
   decodeState 4 6 0x5118ead163,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step9 : Possible adj 4 s8 → Possible adj 4 s9 :=
  advance (unpack 32 0x2bf08cda89e27387e5123df07a4b2fc227b7e6a8) (by rfl)

private def s10 : List (State (Fin 30)) :=
  [decodeState 4 10 0x5118ead161088b7349,
   decodeState 4 7 0x5118ead1610b,
   decodeState 4 6 0x5118ead163,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step10 : Possible adj 4 s9 → Possible adj 4 s10 :=
  advance (unpack 32 0xe550d29f08916efcdb7449f0ddd48fc2385c4977) (by rfl)

private def s11 : List (State (Fin 30)) :=
  [decodeState 4 14 0x5118ead1610b72829a40c38928,
   decodeState 4 13 0x5118ead1610b72829a40c38b,
   decodeState 4 11 0x5118ead1610b72829a43,
   decodeState 4 6 0x5118ead163,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step11 : Possible adj 4 s10 → Possible adj 4 s11 :=
  advance (unpack 32 0x2c7089c1d83ae4d5d4b73e10ba96e7c19f46d49c) (by rfl)

private def s12 : List (State (Fin 30)) :=
  [decodeState 4 19 0x5118ead163088972821028c1b25baa9be330,
   decodeState 4 12 0x5118ead16308897282102b,
   decodeState 4 10 0x5118ead16308897283,
   decodeState 4 9 0x5118ead163088973,
   decodeState 4 8 0x5118ead163088b,
   decodeState 4 7 0x5118ead16309,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step12 : Possible adj 4 s11 → Possible adj 4 s12 :=
  advance (unpack 32 0x372755db05141d109e458f32fde3752bf22e3f75) (by rfl)

private def s13 : List (State (Fin 30)) :=
  [decodeState 4 19 0x5118ead16308897282102ba8a29179c0239a,
   decodeState 4 16 0x5118ead16308897282102ba8a2917a,
   decodeState 4 13 0x5118ead16308897282102baa,
   decodeState 4 10 0x5118ead16308897283,
   decodeState 4 9 0x5118ead163088973,
   decodeState 4 8 0x5118ead163088b,
   decodeState 4 7 0x5118ead16309,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step13 : Possible adj 4 s12 → Possible adj 4 s13 :=
  advance (unpack 32 0x9930f96d187f2787f0ed5e5f844e47c1934abf34) (by rfl)

private def s14 : List (State (Fin 30)) :=
  [decodeState 4 16 0x5118ead163088972834920a26baa28,
   decodeState 4 12 0x5118ead163088972834921,
   decodeState 4 9 0x5118ead163088973,
   decodeState 4 8 0x5118ead163088b,
   decodeState 4 7 0x5118ead16309,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step14 : Possible adj 4 s13 → Possible adj 4 s14 :=
  advance (unpack 32 0x2d5b4271e8cd5b8b96d44e5ebc50d29f11336768) (by rfl)

private def s15 : List (State (Fin 30)) :=
  [decodeState 4 13 0x5118ead16308897348a2d9b2,
   decodeState 4 10 0x5118ead16308897349,
   decodeState 4 8 0x5118ead163088b,
   decodeState 4 7 0x5118ead16309,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step15 : Possible adj 4 s14 → Possible adj 4 s15 :=
  advance (unpack 32 0xb6e89c2246b736fe3d195d5b4362e5e3d195dcd8) (by rfl)

private def s16 : List (State (Fin 30)) :=
  [decodeState 4 13 0x5118ead163088973492131b8,
   decodeState 4 13 0x5118ead163088973492131b9,
   decodeState 4 8 0x5118ead163088b,
   decodeState 4 7 0x5118ead16309,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step16 : Possible adj 4 s15 → Possible adj 4 s16 :=
  advance (unpack 32 0xbf2b72bd195db6da1b8fccf6bab684e550db95f9) (by rfl)

private def s17 : List (State (Fin 30)) :=
  [decodeState 4 13 0x5118ead163088b72821028c1,
   decodeState 4 12 0x5118ead163088b72821029,
   decodeState 4 10 0x5118ead163088b7283,
   decodeState 4 9 0x5118ead163088b73,
   decodeState 4 7 0x5118ead16309,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step17 : Possible adj 4 s16 → Possible adj 4 s17 :=
  advance (unpack 32 0xc14507596d2c9752e11c3c8b8dbf88c6db579647) (by rfl)

private def s18 : List (State (Fin 30)) :=
  [decodeState 4 13 0x5118ead163088b728349e240,
   decodeState 4 13 0x5118ead163088b728349e243,
   decodeState 4 9 0x5118ead163088b73,
   decodeState 4 7 0x5118ead16309,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step18 : Possible adj 4 s17 → Possible adj 4 s18 :=
  advance (unpack 32 0x471772cb956dcafc2336a2789ccd123e2fc9d576) (by rfl)

private def s19 : List (State (Fin 30)) :=
  [decodeState 4 18 0x5118ead163088b7348a2d9b2ca7bb9286b,
   decodeState 4 10 0x5118ead163088b7349,
   decodeState 4 7 0x5118ead16309,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step19 : Possible adj 4 s18 → Possible adj 4 s19 :=
  advance (unpack 32 0x694f8448b77e6dba2706a1e6b7edb6292ada3cd8) (by rfl)

private def s20 : List (State (Fin 30)) :=
  [decodeState 4 8 0x5118ead163096a,
   decodeState 4 8 0x5118ead163096b,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step20 : Possible adj 4 s19 → Possible adj 4 s20 :=
  advance (unpack 32 0x6e0eb935752dcf8460f72daa86d0cfa36a4e72a8) (by rfl)

private def s21 : List (State (Fin 30)) :=
  [decodeState 4 17 0x5118ead163096aa0103823a8727a829a,
   decodeState 4 8 0x5118ead163096b,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step21 : Possible adj 4 s20 → Possible adj 4 s21 :=
  advance (unpack 32 0x9c1eeae51c7d6cbe54b0c4dcf2dea84af0621c54) (by rfl)

private def s22 : List (State (Fin 30)) :=
  [decodeState 4 15 0x5118ead163096b4940caa8b83ac1,
   decodeState 4 13 0x5118ead163096b4940caa8b9,
   decodeState 4 12 0x5118ead163096b4940caaa,
   decodeState 4 10 0x5118ead163096b4942,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step22 : Possible adj 4 s21 → Possible adj 4 s22 :=
  advance (unpack 32 0xc1ef5ca30725cb5e6f07b96027ad19b513c464b8) (by rfl)

private def s23 : List (State (Fin 30)) :=
  [decodeState 4 15 0x5118ead163096b4940caaa5b9be3,
   decodeState 4 10 0x5118ead163096b4942,
   decodeState 4 5 0x5118ead3,
   decodeState 3 3 0x511a]

private theorem step23 : Possible adj 4 s22 → Possible adj 4 s23 :=
  advance (unpack 32 0xe4d7013e027c606b60a4809ef28a12809e5b50c4) (by rfl)

private def s24 : List (State (Fin 30)) :=
  [decodeState 4 16 0x5118ead3a0497282109a3840caa82b,
   decodeState 4 15 0x5118ead3a0497282109a3840caab,
   decodeState 4 13 0x5118ead3a0497282109a3843,
   decodeState 4 12 0x5118ead3a0497282109a3a,
   decodeState 4 7 0x5118ead3a04b,
   decodeState 4 6 0x5118ead3a2,
   decodeState 3 3 0x511a]

private theorem step24 : Possible adj 4 s23 → Possible adj 4 s24 :=
  advance (unpack 32 0xc3cb5ca0f3141c9a3cb1e62462666b808d22162f) (by rfl)

private def s25 : List (State (Fin 30)) :=
  [decodeState 4 17 0x5118ead3a04b1021729a823840ca7bc1,
   decodeState 4 14 0x5118ead3a04b1021729a823843,
   decodeState 4 13 0x5118ead3a04b1021729a823a,
   decodeState 4 9 0x5118ead3a04b1023,
   decodeState 4 8 0x5118ead3a04b12,
   decodeState 4 6 0x5118ead3a2,
   decodeState 3 3 0x511a]

private theorem step25 : Possible adj 4 s24 → Possible adj 4 s25 :=
  advance (unpack 32 0xc3f283c26e20b0fc3cb9aa1af2e3965e1e5b2f0f) (by rfl)

private def s26 : List (State (Fin 30)) :=
  [decodeState 4 10 0x5118ead3a04b102331,
   decodeState 4 10 0x5118ead3a04b102333,
   decodeState 4 8 0x5118ead3a04b12,
   decodeState 4 6 0x5118ead3a2,
   decodeState 3 3 0x511a]

private theorem step26 : Possible adj 4 s25 → Possible adj 4 s26 :=
  advance (unpack 32 0x3478fc2ec5d9a565970fca1b1e66af2d9785daa5) (by rfl)

private def s27 : List (State (Fin 30)) :=
  [decodeState 4 16 0x5118ead3a04b10233338aa59bbc279,
   decodeState 4 11 0x5118ead3a04b1023333a,
   decodeState 4 8 0x5118ead3a04b12,
   decodeState 4 6 0x5118ead3a2,
   decodeState 3 3 0x511a]

private theorem step27 : Possible adj 4 s26 → Possible adj 4 s27 :=
  advance (unpack 32 0x7e2ebc3f0f2f1f85dea7cbd059372f2a3078566e) (by rfl)

private def s28 : List (State (Fin 30)) :=
  [decodeState 4 16 0x5118ead3a04b1023333a69910b61c0,
   decodeState 4 8 0x5118ead3a04b12,
   decodeState 4 6 0x5118ead3a2,
   decodeState 3 3 0x511a]

private theorem step28 : Possible adj 4 s27 → Possible adj 4 s28 :=
  advance (unpack 32 0xc3388ddb157aeb82ed187f23c46ed8abcb70c9bc) (by rfl)

private def s29 : List (State (Fin 30)) :=
  [decodeState 4 18 0x5118ead3a04b1269812333910b61b83ac0,
   decodeState 4 16 0x5118ead3a04b1269812333910b61bb,
   decodeState 4 6 0x5118ead3a2,
   decodeState 3 3 0x511a]

private theorem step29 : Possible adj 4 s28 → Possible adj 4 s29 :=
  advance (unpack 32 0xc1eeca96e7c239b78646241bb7d51c8df68e3ea5) (by rfl)

private def s30 : List (State (Fin 30)) :=
  [decodeState 4 17 0x5118ead3a2103871bb69dbb259c82333,
   decodeState 4 15 0x5118ead3a2103871bb69dbb259ca,
   decodeState 4 9 0x5118ead3a2103872,
   decodeState 4 8 0x5118ead3a2103a,
   decodeState 4 7 0x5118ead3a212,
   decodeState 3 3 0x511a]

private theorem step30 : Possible adj 4 s29 → Possible adj 4 s30 :=
  advance (unpack 32 0x3132b79709312db6ddc7171f52f11b7d4b8e236f) (by rfl)

private def s31 : List (State (Fin 30)) :=
  [decodeState 4 18 0x5118ead3a21038729a40caa8b079c32a81,
   decodeState 4 15 0x5118ead3a21038729a40caa8b07b,
   decodeState 4 14 0x5118ead3a21038729a40caa8b2,
   decodeState 4 13 0x5118ead3a21038729a40caab,
   decodeState 4 11 0x5118ead3a21038729a43,
   decodeState 4 8 0x5118ead3a2103a,
   decodeState 4 7 0x5118ead3a212,
   decodeState 3 3 0x511a]

private theorem step31 : Possible adj 4 s30 → Possible adj 4 s31 :=
  advance (unpack 32 0x8170fb5728dd4bc7e4d85bcb8312cdbcebc2bf08) (by rfl)

private def s32 : List (State (Fin 30)) :=
  [decodeState 4 21 0x5118ead3a21038729a43c15ab069334bbb2a7b08,
   decodeState 4 8 0x5118ead3a2103a,
   decodeState 4 7 0x5118ead3a212,
   decodeState 3 3 0x511a]

private theorem step32 : Possible adj 4 s31 → Possible adj 4 s32 :=
  advance (unpack 32 0xbcb7499b65e0902d9780bf72bb70fc3ca481706) (by rfl)

private def s33 : List (State (Fin 30)) :=
  [decodeState 4 15 0x5118ead3a2103a71db0b696120aa,
   decodeState 4 14 0x5118ead3a2103a71db0b696123,
   decodeState 4 9 0x5118ead3a2103a72,
   decodeState 4 7 0x5118ead3a212,
   decodeState 3 3 0x511a]

private theorem step33 : Possible adj 4 s32 → Possible adj 4 s33 :=
  advance (unpack 32 0xa918d796516e38b31139e5ea57aec6c6501dba04) (by rfl)

private def s34 : List (State (Fin 30)) :=
  [decodeState 4 18 0x5118ead3a2103a7299b04b233369912a79,
   decodeState 4 17 0x5118ead3a2103a7299b04b233369912b,
   decodeState 4 11 0x5118ead3a2103a7299b2,
   decodeState 4 10 0x5118ead3a2103a729a,
   decodeState 4 7 0x5118ead3a212,
   decodeState 3 3 0x511a]

private theorem step34 : Possible adj 4 s33 → Possible adj 4 s34 :=
  advance (unpack 32 0x7964d311369c8af9c57c46305af1e8caec67f32b) (by rfl)

private def s35 : List (State (Fin 30)) :=
  [decodeState 4 18 0x5118ead3a2103a7299b2ca084079c328bb,
   decodeState 4 15 0x5118ead3a2103a7299b2ca08407b,
   decodeState 4 14 0x5118ead3a2103a7299b2ca0843,
   decodeState 4 13 0x5118ead3a2103a7299b2ca0b,
   decodeState 4 10 0x5118ead3a2103a729a,
   decodeState 4 7 0x5118ead3a212,
   decodeState 3 3 0x511a]

private theorem step35 : Possible adj 4 s34 → Possible adj 4 s35 :=
  advance (unpack 32 0xb970f4051b7f2372cb0623569ced187f237da31c) (by rfl)

private def s36 : List (State (Fin 30)) :=
  [decodeState 4 15 0x5118ead3a2103a729a40caa8b07b,
   decodeState 4 14 0x5118ead3a2103a729a40caa8b2,
   decodeState 4 13 0x5118ead3a2103a729a40caab,
   decodeState 4 11 0x5118ead3a2103a729a43,
   decodeState 4 7 0x5118ead3a212,
   decodeState 3 3 0x511a]

private theorem step36 : Possible adj 4 s35 → Possible adj 4 s36 :=
  advance (unpack 32 0x340b87dab942305aedbc7af6f2c9b85aee5c6ebc) (by rfl)

private def s37 : List (State (Fin 30)) :=
  [decodeState 4 19 0x5118ead3a2103a729a436991d9b04b332b7a,
   decodeState 4 15 0x5118ead3a2103a729a436991d9b2,
   decodeState 4 7 0x5118ead3a212,
   decodeState 3 3 0x511a]

private theorem step37 : Possible adj 4 s36 → Possible adj 4 s37 :=
  advance (unpack 32 0x7c081794c9b6e4d240b65e02fdc9b87e1e5240b8) (by rfl)

private def s38 : List (State (Fin 30)) :=
  [decodeState 4 23 0x5118ead3a212810838bb69b22859c82333aac2434b79,
   decodeState 4 16 0x5118ead3a212810838bb69b22859ca,
   decodeState 4 10 0x5118ead3a21281083a,
   decodeState 4 9 0x5118ead3a212810b,
   decodeState 3 3 0x511a]

private theorem step38 : Possible adj 4 s37 → Possible adj 4 s38 :=
  advance (unpack 32 0x7a518a9899595f8aa4c5259b738611e65e5c2e3c) (by rfl)

private def s39 : List (State (Fin 30)) :=
  [decodeState 4 15 0x5118ead3a21281083a48b2ca4359,
   decodeState 4 11 0x5118ead3a21281083a4b,
   decodeState 4 9 0x5118ead3a212810b,
   decodeState 3 3 0x511a]

private theorem step39 : Possible adj 4 s38 → Possible adj 4 s39 :=
  advance (unpack 32 0x5bf17e576f361772a3364edd8dd78fc71f5db91b) (by rfl)

private def s40 : List (State (Fin 30)) :=
  [decodeState 4 18 0x5118ead3a21281083a4b692379e2a8db40,
   decodeState 4 9 0x5118ead3a212810b,
   decodeState 3 3 0x511a]

private theorem step40 : Possible adj 4 s39 → Possible adj 4 s40 :=
  advance (unpack 32 0x46ebc7edf735518e576fb99182af362376f35cb8) (by rfl)

private def s41 : List (State (Fin 30)) :=
  [decodeState 4 21 0x5118ead3a212810b696123339148b259ca28bbc2,
   decodeState 4 19 0x5118ead3a212810b696123339148b259ca2b,
   decodeState 4 15 0x5118ead3a212810b69612333914b,
   decodeState 3 3 0x511a]

private theorem step41 : Possible adj 4 s40 → Possible adj 4 s41 :=
  advance (unpack 32 0xc5cb95d932c1eefe54b95d8dbaf1767918db14d8) (by rfl)

private def s42 : List (State (Fin 30)) :=
  [decodeState 3 8 0x511a6999d25991,
   decodeState 4 8 0x511a6999d25993,
   decodeState 4 7 0x511a6999d25b,
   decodeState 4 6 0x511a6999d3,
   decodeState 4 5 0x511a699b,
   decodeState 4 4 0x511a6b]

private theorem step42 : Possible adj 4 s41 → Possible adj 4 s42 :=
  advance (unpack 32 0x92f536f1f52f11b7d4b8e236fc1eefda307bbf95) (by rfl)

private def s43 : List (State (Fin 30)) :=
  [decodeState 4 15 0x511a6999d25991c823e8a0b0e17a,
   decodeState 4 14 0x511a6999d25991c823e8a0b0e3,
   decodeState 4 9 0x511a6999d25991cb,
   decodeState 4 8 0x511a6999d25993,
   decodeState 4 7 0x511a6999d25b,
   decodeState 4 6 0x511a6999d3,
   decodeState 4 5 0x511a699b,
   decodeState 4 4 0x511a6b]

private theorem step43 : Possible adj 4 s42 → Possible adj 4 s43 :=
  advance (unpack 32 0x7f2d4ed4b8450573a78f3c526762c6c145c7ec99) (by rfl)

private def s44 : List (State (Fin 30)) :=
  [decodeState 4 18 0x511a6999d25991cb226189e3a830eba3d9,
   decodeState 4 15 0x511a6999d25991cb226189e3a832,
   decodeState 4 12 0x511a6999d25991cb22618a,
   decodeState 4 11 0x511a6999d25991cb2262,
   decodeState 4 8 0x511a6999d25993,
   decodeState 4 7 0x511a6999d25b,
   decodeState 4 6 0x511a6999d3,
   decodeState 4 5 0x511a699b,
   decodeState 4 4 0x511a6b]

private theorem step44 : Possible adj 4 s43 → Possible adj 4 s44 :=
  advance (unpack 32 0xdd3a6af22cc16cf76e9d22305bc047dbc3b3bb05) (by rfl)

private def s45 : List (State (Fin 30)) :=
  [decodeState 4 21 0x511a6999d25991cb22618adb1079e338baa0324a,
   decodeState 4 11 0x511a6999d25991cb2262,
   decodeState 4 8 0x511a6999d25993,
   decodeState 4 7 0x511a6999d25b,
   decodeState 4 6 0x511a6999d3,
   decodeState 4 5 0x511a699b,
   decodeState 4 4 0x511a6b]

private theorem step45 : Possible adj 4 s44 → Possible adj 4 s45 :=
  advance (unpack 32 0x49a973f1e2b1b057ef05b9de23dca1c3f762e1ee) (by rfl)

private def s46 : List (State (Fin 30)) :=
  [decodeState 4 8 0x511a6999d25993,
   decodeState 4 7 0x511a6999d25b,
   decodeState 4 6 0x511a6999d3,
   decodeState 4 5 0x511a699b,
   decodeState 4 4 0x511a6b]

private theorem step46 : Possible adj 4 s45 → Possible adj 4 s46 :=
  advance (unpack 32 0xa9707eb83c78b057eea5ba4d4c1faedbc3c8d4b8) (by rfl)

private def s47 : List (State (Fin 30)) :=
  [decodeState 4 19 0x511a6999d25bb04a22a83208eb1038c17b2a,
   decodeState 4 16 0x511a6999d25bb04a22a83208eb103b,
   decodeState 4 15 0x511a6999d25bb04a22a83208eb13,
   decodeState 4 13 0x511a6999d25bb04a22a8320a,
   decodeState 4 12 0x511a6999d25bb04a22a833,
   decodeState 4 10 0x511a6999d25bb04a23,
   decodeState 4 6 0x511a6999d3,
   decodeState 4 5 0x511a699b,
   decodeState 4 4 0x511a6b]

private theorem step47 : Possible adj 4 s46 → Possible adj 4 s47 :=
  advance (unpack 32 0x2bf0717426a9136bf1e5b43b9a96e9e3c98388d4) (by rfl)

private def s48 : List (State (Fin 30)) :=
  [decodeState 4 16 0x511a6999d25bb04a22a83391c8e80a,
   decodeState 4 10 0x511a6999d25bb04a23,
   decodeState 4 6 0x511a6999d3,
   decodeState 4 5 0x511a699b,
   decodeState 4 4 0x511a6b]

private theorem step48 : Possible adj 4 s47 → Possible adj 4 s48 :=
  advance (unpack 32 0xf7327ef0ce44b27ed1863cb8b9c5b7f22593f77) (by rfl)

private def s49 : List (State (Fin 30)) :=
  [decodeState 4 17 0x511a6999d3e822a0b0c8e17bd9700a29,
   decodeState 4 17 0x511a6999d3e822a0b0c8e17bd9700a2a,
   decodeState 4 12 0x511a6999d3e822a0b0c8e3,
   decodeState 4 8 0x511a6999d3e823,
   decodeState 4 5 0x511a699b,
   decodeState 4 4 0x511a6b]

private theorem step49 : Possible adj 4 s48 → Possible adj 4 s49 :=
  advance (unpack 32 0x285db7f336a13a8c1c5b916ef0f734460e2dbcb7) (by rfl)

private def s50 : List (State (Fin 30)) :=
  [decodeState 4 18 0x511a6999d3e82332a0b0c8e30aba384279,
   decodeState 4 9 0x511a6999d3e82333,
   decodeState 4 5 0x511a699b,
   decodeState 4 4 0x511a6b]

private theorem step50 : Possible adj 4 s49 → Possible adj 4 s50 :=
  advance (unpack 32 0x7a0f70c4f82c16113f99b50d82bd07b86ebc1b12) (by rfl)

private def s51 : List (State (Fin 30)) :=
  [decodeState 4 19 0x511a6999d3e82333914b59e1d970c2782b8a,
   decodeState 4 14 0x511a6999d3e82333914b59e1db,
   decodeState 4 5 0x511a699b,
   decodeState 4 4 0x511a6b]

private theorem step51 : Possible adj 4 s50 → Possible adj 4 s51 :=
  advance (unpack 32 0x895f876f8b89f022bd7c460e5bf36f0d3364cb05) (by rfl)

private def s52 : List (State (Fin 30)) :=
  [decodeState 4 12 0x511a699b48eb6173d98389,
   decodeState 4 12 0x511a699b48eb6173d9838a,
   decodeState 4 8 0x511a699b48eb62,
   decodeState 4 6 0x511a699b4a,
   decodeState 4 4 0x511a6b]

private theorem step52 : Possible adj 4 s51 → Possible adj 4 s52 :=
  advance (unpack 32 0x8e0b82be54caeda86e9bd399d4bf0fc14f878a22) (by rfl)

private def s53 : List (State (Fin 30)) :=
  [decodeState 4 8 0x511a699b48eb62,
   decodeState 4 6 0x511a699b4a,
   decodeState 4 4 0x511a6b]

private theorem step53 : Possible adj 4 s52 → Possible adj 4 s53 :=
  advance (unpack 32 0xc3cb2a6576c3cb6c17057af54c3cb6c17057ae5c) (by rfl)

private def s54 : List (State (Fin 30)) :=
  [decodeState 4 21 0x511a699b4ad10873d983eb8a1028aab359c240cb,
   decodeState 4 15 0x511a699b4ad10873d983eb8a1029,
   decodeState 4 8 0x511a699b4ad10a,
   decodeState 4 7 0x511a699b4ad2,
   decodeState 4 4 0x511a6b]

private theorem step54 : Possible adj 4 s53 → Possible adj 4 s54 :=
  advance (unpack 32 0xca30bb54a2b2d982bf91ec36e0e9e5c2ddbcda54) (by rfl)

private def s55 : List (State (Fin 30)) :=
  [decodeState 4 14 0x511a699b4ad10a619132bad928,
   decodeState 4 14 0x511a699b4ad10a619132bad92b,
   decodeState 4 13 0x511a699b4ad10a619132badb,
   decodeState 4 10 0x511a699b4ad10a6193,
   decodeState 4 9 0x511a699b4ad10a63,
   decodeState 4 7 0x511a699b4ad2,
   decodeState 4 4 0x511a6b]

private theorem step55 : Possible adj 4 s54 → Possible adj 4 s55 :=
  advance (unpack 32 0x2ef91ee615415f8dbaf979618db8d263f28c1e4f) (by rfl)

private def s56 : List (State (Fin 30)) :=
  [decodeState 4 17 0x511a699b4ad10a6193a021ba38287bc2,
   decodeState 4 15 0x511a699b4ad10a6193a021ba3829,
   decodeState 4 12 0x511a699b4ad10a6193a022,
   decodeState 4 9 0x511a699b4ad10a63,
   decodeState 4 7 0x511a699b4ad2,
   decodeState 4 4 0x511a6b]

private theorem step56 : Possible adj 4 s55 → Possible adj 4 s56 :=
  advance (unpack 32 0xc3ca7ec79bcc10fc38f7252a4a438b79707c3f0f) (by rfl)

private def s57 : List (State (Fin 30)) :=
  [decodeState 4 14 0x511a699b4ad10a6193a022a8ba,
   decodeState 4 9 0x511a699b4ad10a63,
   decodeState 4 7 0x511a699b4ad2,
   decodeState 4 4 0x511a6b]

private theorem step57 : Possible adj 4 s56 → Possible adj 4 s57 :=
  advance (unpack 32 0xe47b97ee08c38f7ae6227e33113f028bf2836506) (by rfl)

private def s58 : List (State (Fin 30)) :=
  [decodeState 4 11 0x511a699b4ad208eb89e3,
   decodeState 4 10 0x511a699b4ad208eb8a,
   decodeState 4 8 0x511a699b4ad20a,
   decodeState 4 4 0x511a6b]

private theorem step58 : Possible adj 4 s57 → Possible adj 4 s58 :=
  advance (unpack 32 0xe47a179707bf519b533113f19889f8145f9418e5) (by rfl)

private def s59 : List (State (Fin 30)) :=
  [decodeState 4 24 0x511a699b4ad208eb89e391db711038a02232c35979ba28,
   decodeState 4 12 0x511a699b4ad208eb89e393,
   decodeState 4 10 0x511a699b4ad208eb8a,
   decodeState 4 8 0x511a699b4ad20a,
   decodeState 4 4 0x511a6b]

private theorem step59 : Possible adj 4 s58 → Possible adj 4 s59 :=
  advance (unpack 32 0x2ddebc1894389d65e0b0c2cb6258903170c73f72) (by rfl)

private def s60 : List (State (Fin 30)) :=
  [decodeState 4 16 0x511a699b4ad208eb8a91db711038ba,
   decodeState 4 11 0x511a699b4ad208eb8a93,
   decodeState 4 8 0x511a699b4ad20a,
   decodeState 4 4 0x511a6b]

private theorem step60 : Possible adj 4 s59 → Possible adj 4 s60 :=
  advance (unpack 32 0xb9c4eb120fc99ecc2ec576e4fc38955d8b7a1c55) (by rfl)

private def s61 : List (State (Fin 30)) :=
  [decodeState 4 12 0x511a699b4ad20a619130b3,
   decodeState 4 11 0x511a699b4ad20a619132,
   decodeState 4 10 0x511a699b4ad20a6193,
   decodeState 4 9 0x511a699b4ad20a63,
   decodeState 4 4 0x511a6b]

private theorem step61 : Possible adj 4 s60 → Possible adj 4 s61 :=
  advance (unpack 32 0xb1a4cca0d8796b97a2cb2e21b7129738aa5c1894) (by rfl)

private def s62 : List (State (Fin 30)) :=
  [decodeState 4 21 0x511a699b4ad20a619132badb1079e338c32859a0,
   decodeState 4 10 0x511a699b4ad20a6193,
   decodeState 4 9 0x511a699b4ad20a63,
   decodeState 4 4 0x511a6b]

private theorem step62 : Possible adj 4 s61 → Possible adj 4 s62 :=
  advance (unpack 32 0xa2cb83f1e2c3f0f2ef912bf1b3dcf88dcafdd32b) (by rfl)

private def s63 : List (State (Fin 30)) :=
  [decodeState 4 7 0x511a6b9948a2,
   decodeState 4 6 0x511a6b994a,
   decodeState 4 5 0x511a6b9b]

private theorem step63 : Possible adj 4 s62 → Possible adj 4 s63 :=
  advance (unpack 32 0xa266f2e119b52e716506c3cb5ca0d87929738aa4) (by rfl)

private def s64 : List (State (Fin 30)) :=
  [decodeState 4 13 0x511a6b994aa00a1022a833b0,
   decodeState 4 10 0x511a6b994aa00a1023,
   decodeState 4 9 0x511a6b994aa00a12,
   decodeState 4 5 0x511a6b9b]

private theorem step64 : Possible adj 4 s63 → Possible adj 4 s64 :=
  advance (unpack 32 0xb77577e1f82dce6a904fc3f05bd4e2d189d0d3ba) (by rfl)

private def s65 : List (State (Fin 30)) :=
  [decodeState 4 8 0x511a6b9ba0e810,
   decodeState 4 8 0x511a6b9ba0e812,
   decodeState 4 7 0x511a6b9ba0eb,
   decodeState 4 6 0x511a6b9ba2]

private theorem step65 : Possible adj 4 s64 → Possible adj 4 s65 :=
  advance (unpack 32 0x1768fc3f053dfa8cdb582bcf7ea33679707bf519) (by rfl)

private def s66 : List (State (Fin 30)) :=
  [decodeState 4 11 0x511a6b9ba0e810385b83,
   decodeState 4 9 0x511a6b9ba0e8103a,
   decodeState 4 8 0x511a6b9ba0e812,
   decodeState 4 7 0x511a6b9ba0eb,
   decodeState 4 6 0x511a6b9ba2]

private theorem step66 : Possible adj 4 s65 → Possible adj 4 s66 :=
  advance (unpack 32 0xb97997e0c1b1210362c5a91e4ad8afc233748567) (by rfl)

private def s67 : List (State (Fin 30)) :=
  [decodeState 4 19 0x511a6b9ba0e8103ab95b83e389d170c17a21,
   decodeState 4 16 0x511a6b9ba0e8103ab95b83e389d173,
   decodeState 4 8 0x511a6b9ba0e812,
   decodeState 4 7 0x511a6b9ba0eb,
   decodeState 4 6 0x511a6b9ba2]

private theorem step67 : Possible adj 4 s66 → Possible adj 4 s67 :=
  advance (unpack 32 0x23f0ed47905dd3c7e0c4c3f0f2dcb84653b78796) (by rfl)

private def s68 : List (State (Fin 30)) :=
  [decodeState 4 20 0x511a6b9ba0e812d1590a4aba382132c378298b,
   decodeState 4 15 0x511a6b9ba0e812d1590a4aba3822,
   decodeState 4 10 0x511a6b9ba0e812d15b,
   decodeState 4 7 0x511a6b9ba0eb,
   decodeState 4 6 0x511a6b9ba2]

private theorem step68 : Possible adj 4 s67 → Possible adj 4 s68 :=
  advance (unpack 32 0x895f8c3d198e5187964621ee90af58358afdd8c5) (by rfl)

private def s69 : List (State (Fin 30)) :=
  [decodeState 4 16 0x511a6b9ba0e812d15b70e389782b80,
   decodeState 4 14 0x511a6b9ba0e812d15b70e38979,
   decodeState 4 11 0x511a6b9ba0e812d15b73,
   decodeState 4 7 0x511a6b9ba0eb,
   decodeState 4 6 0x511a6b9ba2]

private theorem step69 : Possible adj 4 s68 → Possible adj 4 s69 :=
  advance (unpack 32 0x83326c58af8dcb8459f94863c748d87e119896b9) (by rfl)

private def s70 : List (State (Fin 30)) :=
  [decodeState 4 18 0x511a6b9ba0e812d15b73d9e378892ab0c1,
   decodeState 4 16 0x511a6b9ba0e812d15b73d9e378892b,
   decodeState 4 7 0x511a6b9ba0eb,
   decodeState 4 6 0x511a6b9ba2]

private theorem step70 : Possible adj 4 s69 → Possible adj 4 s70 :=
  advance (unpack 32 0xc58b17a307916efb65218f3722d50731318664d2) (by rfl)

private def s71 : List (State (Fin 30)) :=
  [decodeState 4 17 0x511a6b9ba0eb1038594abacb7922a82b,
   decodeState 4 14 0x511a6b9ba0eb1038594abacb7a,
   decodeState 4 10 0x511a6b9ba0eb10385b,
   decodeState 4 9 0x511a6b9ba0eb103a,
   decodeState 4 8 0x511a6b9ba0eb12,
   decodeState 4 6 0x511a6b9ba2]

private theorem step71 : Possible adj 4 s70 → Possible adj 4 s71 :=
  advance (unpack 32 0x2d48f7102f785c4ad8b8466e959c58664d283326) (by rfl)

private def s72 : List (State (Fin 30)) :=
  [decodeState 4 12 0x511a6b9ba0eb10385b83b2,
   decodeState 4 9 0x511a6b9ba0eb103a,
   decodeState 4 8 0x511a6b9ba0eb12,
   decodeState 4 6 0x511a6b9ba2]

private theorem step72 : Possible adj 4 s71 → Possible adj 4 s72 :=
  advance (unpack 32 0xc3f0f2a32fc1629e5a25cf1f8358907103881b16) (by rfl)

private def s73 : List (State (Fin 30)) :=
  [decodeState 4 17 0x511a6b9ba0eb126189e3d1594a21780a,
   decodeState 4 15 0x511a6b9ba0eb126189e3d1594a22,
   decodeState 4 13 0x511a6b9ba0eb126189e3d15b,
   decodeState 4 6 0x511a6b9ba2]

private theorem step73 : Possible adj 4 s72 → Possible adj 4 s73 :=
  advance (unpack 32 0xbc895eb9166de57636f716e95c35c8b13c7e0c4) (by rfl)

private def s74 : List (State (Fin 30)) :=
  [decodeState 4 15 0x511a6b9ba0eb126189e3d15b73d9,
   decodeState 4 6 0x511a6b9ba2]

private theorem step74 : Possible adj 4 s73 → Possible adj 4 s74 :=
  advance (unpack 32 0xdd48f2c8d876deec1a50dbd1875cb5c1a57760b9) (by rfl)

private def s75 : List (State (Fin 30)) :=
  [decodeState 4 12 0x511a6b9ba2d12131934873,
   decodeState 4 11 0x511a6b9ba2d121319349]

private theorem step75 : Possible adj 4 s74 → Possible adj 4 s75 :=
  advance (unpack 32 0x7264f2e3916777071b057ef916760e268d28170f) (by rfl)

private def s76 : List (State (Fin 30)) :=
  []

private theorem step76 : Possible adj 4 s75 → Possible adj 4 s76 :=
  advance (unpack 31 0x61f8797b87e1e56478bc3cb6c3f0f2af916761b) (by rfl)

private theorem lower : ¬ Colorable (cycleGraph 9) 4 := by
  let S : Fin 30 → Finset (Fin 9) := fun i => #v[{0, 2, 4}, {0, 2, 5}, {0, 2, 6}, {0, 2, 7}, {0, 3, 5}, {0, 3, 6},
    {0, 3, 7}, {0, 4, 6}, {0, 4, 7}, {0, 5, 7}, {1, 3, 5}, {1, 3, 6},
    {1, 3, 7}, {1, 3, 8}, {1, 4, 6}, {1, 4, 7}, {1, 4, 8}, {1, 5, 7},
    {1, 5, 8}, {1, 6, 8}, {2, 4, 6}, {2, 4, 7}, {2, 4, 8}, {2, 5, 7},
    {2, 5, 8}, {2, 6, 8}, {3, 5, 7}, {3, 5, 8}, {3, 6, 8}, {4, 6, 8}][i]
  have hs : ∀ i, StableTriple (cycleGraph _) (S i) := by unfold StableTriple; decide +kernel
  have he : ∀ i j, adj i j → Disjoint (S i) (S j) := by decide +kernel
  rintro ⟨c, hc⟩
  have h0 : Possible adj 4 s0 := possible_start (fun i => c ⟨S i, hs i⟩)
    (fun i j hij => hc _ _ (he i j hij))
  have h1 := step1 h0
  have h2 := step2 h1
  have h3 := step3 h2
  have h4 := step4 h3
  have h5 := step5 h4
  have h6 := step6 h5
  have h7 := step7 h6
  have h8 := step8 h7
  have h9 := step9 h8
  have h10 := step10 h9
  have h11 := step11 h10
  have h12 := step12 h11
  have h13 := step13 h12
  have h14 := step14 h13
  have h15 := step15 h14
  have h16 := step16 h15
  have h17 := step17 h16
  have h18 := step18 h17
  have h19 := step19 h18
  have h20 := step20 h19
  have h21 := step21 h20
  have h22 := step22 h21
  have h23 := step23 h22
  have h24 := step24 h23
  have h25 := step25 h24
  have h26 := step26 h25
  have h27 := step27 h26
  have h28 := step28 h27
  have h29 := step29 h28
  have h30 := step30 h29
  have h31 := step31 h30
  have h32 := step32 h31
  have h33 := step33 h32
  have h34 := step34 h33
  have h35 := step35 h34
  have h36 := step36 h35
  have h37 := step37 h36
  have h38 := step38 h37
  have h39 := step39 h38
  have h40 := step40 h39
  have h41 := step41 h40
  have h42 := step42 h41
  have h43 := step43 h42
  have h44 := step44 h43
  have h45 := step45 h44
  have h46 := step46 h45
  have h47 := step47 h46
  have h48 := step48 h47
  have h49 := step49 h48
  have h50 := step50 h49
  have h51 := step51 h50
  have h52 := step52 h51
  have h53 := step53 h52
  have h54 := step54 h53
  have h55 := step55 h54
  have h56 := step56 h55
  have h57 := step57 h56
  have h58 := step58 h57
  have h59 := step59 h58
  have h60 := step60 h59
  have h61 := step61 h60
  have h62 := step62 h61
  have h63 := step63 h62
  have h64 := step64 h63
  have h65 := step65 h64
  have h66 := step66 h65
  have h67 := step67 h66
  have h68 := step68 h67
  have h69 := step69 h68
  have h70 := step70 h69
  have h71 := step71 h70
  have h72 := step72 h71
  have h73 := step73 h72
  have h74 := step74 h73
  have h75 := step75 h74
  have h76 := step76 h75
  obtain ⟨s, hs', _⟩ := h76
  cases hs'

end Cycle9Cert

theorem cycle9_tight : K3Tight (cycleGraph 9) :=
  ⟨Cycle9Cert.lower, upper_bound _ (by decide)⟩

end StableKneserK3
