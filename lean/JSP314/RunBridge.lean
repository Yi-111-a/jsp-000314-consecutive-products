import JSP314.RunDecomp
import JSP314.JointSieve

/-!
# JSP-000314 — bridge from run witnesses to the jointly sifted set

Each right run witness `m` (a `p²`-multiple with `largestPrimeFactor m = p`
whose `k` right neighbours are all `p`-smooth) has the form `m = p²·r` with
`r ∈ [1, 2x/p²]`, and the smoothness of `m + j` forbids every sifted prime
`q ∈ (p, w]` from dividing `p²·r + j`: otherwise `q` would be a prime factor
of `m + j` larger than its largest prime factor.  Hence `m ↦ m / p²` injects
`rightRunWitness x p k` into `siftedSet (2x/p²) p k w`:

* `rightRunCount_le_siftedSet_card` —
  `rightRunCount x p k ≤ (siftedSet (2x/p²) p k w).card`.

For the left runs the neighbours are `m - j = p²·r - j`, which is a genuine
(non-truncated) subtraction once `j ≤ k < p² ≤ m`; the same argument injects
`leftRunWitness x p k` into `leftSiftedSet (2x/p²) p k w`:

* `leftRunCount_le_leftSiftedSet_card` —
  `leftRunCount x p k ≤ (leftSiftedSet (2x/p²) p k w).card` for `k < p²`.

The strict bound `k < p²` is needed so that `m - j ≥ 1`: at `k = p²` a
hypothetical witness `m = p²` would give `m - j = 0`, which every `q`
divides, so the sifted condition could never hold there.
-/

namespace JSP314

open Finset

/-- Auxiliary: a number whose largest prime factor is the prime `p` is at
least `2`.  (Local copy of the identically-named lemma, kept private so this
file does not depend on unbuilt modules.) -/
private theorem two_le_of_lpf_eq {p m : ℕ} (hp : p.Prime)
    (h : largestPrimeFactor m = p) : 2 ≤ m := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have h1 : largestPrimeFactor m = 1 :=
      largestPrimeFactor_eq_one_iff.mpr (by omega)
    have h2 := hp.two_le
    omega
  · exact hm

/-- **Right bridge**: the right run witnesses inject via `m ↦ m / p²` into
the jointly sifted set on `[1, 2x/p²]`.  Every sifted prime `q ∈ (p, w]`
avoiding `p²r + 1, …, p²r + k` is forced, because `q ∣ m + j` would give
`q ≤ largestPrimeFactor (m + j) ≤ p`, contradicting `p < q`. -/
theorem rightRunCount_le_siftedSet_card {x p k w : ℕ} (hp : p.Prime) :
    rightRunCount x p k ≤ (siftedSet (2 * x / p ^ 2) p k w).card := by
  classical
  rw [rightRunCount]
  apply Finset.card_le_card_of_injOn (fun m => m / p ^ 2)
  · intro m hm
    rw [Finset.mem_coe, mem_rightRunWitness] at hm
    obtain ⟨hm2x, hpdvd, hlpf, harc⟩ := hm
    have hm2 : 2 ≤ m := two_le_of_lpf_eq hp hlpf
    have hmpos : 0 < m := by omega
    have hp2pos : 0 < p ^ 2 := pow_pos hp.pos 2
    have hr1 : 1 ≤ m / p ^ 2 := by
      have h := Nat.div_pos (Nat.le_of_dvd hmpos hpdvd) hp2pos
      omega
    have hry : m / p ^ 2 ≤ 2 * x / p ^ 2 := Nat.div_le_div_right hm2x
    rw [Finset.mem_coe]
    simp only [siftedSet, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hr1, hry⟩, ?_⟩
    intro q hq j hj hdvd
    rw [Finset.mem_Ioc] at hq
    obtain ⟨⟨hpq, -⟩, hqpr⟩ := hq
    rw [Nat.mul_div_cancel' hpdvd] at hdvd
    have hmem : m + j ∈ Finset.Icc (m + 1) (m + k) :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hle := harc (m + j) hmem
    have hqle :=
      prime_dvd_le_largestPrimeFactor (by omega : 2 ≤ m + j) hqpr hdvd
    omega
  · intro a ha b hb hab
    rw [Finset.mem_coe, mem_rightRunWitness] at ha hb
    calc a = p ^ 2 * (a / p ^ 2) := (Nat.mul_div_cancel' ha.2.1).symm
      _ = p ^ 2 * (b / p ^ 2) := by rw [show a / p ^ 2 = b / p ^ 2 from hab]
      _ = b := Nat.mul_div_cancel' hb.2.1

/-- **Left sifted set**: `r ∈ [1, y]` such that for every prime `q` with
`p < q ≤ w`, none of `p²·r - 1, …, p²·r - k` is divisible by `q`. -/
def leftSiftedSet (y p k w : ℕ) : Finset ℕ :=
  (Finset.Icc 1 y).filter fun r =>
    ∀ q ∈ (Finset.Ioc p w).filter Nat.Prime, ∀ j ∈ Finset.Icc 1 k,
      ¬ q ∣ p ^ 2 * r - j

/-- **Left bridge**: for `k < p²` the left run witnesses inject via
`m ↦ m / p²` into `leftSiftedSet (2x/p²) p k w`.  Here `m - j = p²r - j` is
a genuine subtraction (`j ≤ k < p² ≤ m`), so `q ∣ m - j` either forces
`m - j = 1` (impossible for `q ≥ 2`) or `q ≤ largestPrimeFactor (m - j) ≤ p`,
contradicting `p < q`. -/
theorem leftRunCount_le_leftSiftedSet_card {x p k w : ℕ} (hp : p.Prime)
    (hk : k < p ^ 2) :
    leftRunCount x p k ≤ (leftSiftedSet (2 * x / p ^ 2) p k w).card := by
  classical
  rw [leftRunCount]
  apply Finset.card_le_card_of_injOn (fun m => m / p ^ 2)
  · intro m hm
    rw [Finset.mem_coe, mem_leftRunWitness] at hm
    obtain ⟨hm2x, hpdvd, hlpf, harc⟩ := hm
    have hm2 : 2 ≤ m := two_le_of_lpf_eq hp hlpf
    have hmpos : 0 < m := by omega
    have hp2pos : 0 < p ^ 2 := pow_pos hp.pos 2
    have hmge : p ^ 2 ≤ m := Nat.le_of_dvd hmpos hpdvd
    have hr1 : 1 ≤ m / p ^ 2 := by
      have h := Nat.div_pos hmge hp2pos
      omega
    have hry : m / p ^ 2 ≤ 2 * x / p ^ 2 := Nat.div_le_div_right hm2x
    rw [Finset.mem_coe]
    simp only [leftSiftedSet, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hr1, hry⟩, ?_⟩
    intro q hq j hj hdvd
    rw [Finset.mem_Ioc] at hq
    obtain ⟨⟨hpq, -⟩, hqpr⟩ := hq
    rw [Nat.mul_div_cancel' hpdvd] at hdvd
    have hmj1 : 1 ≤ m - j := by omega
    have hmem : m - j ∈ Finset.Icc (m - k) (m - 1) := by
      rw [Finset.mem_Icc]
      refine ⟨Nat.sub_le_sub_left hj.2 m, by omega⟩
    have hle := harc (m - j) hmem
    rcases Nat.lt_or_ge (m - j) 2 with hsmall | hbig
    · have hmj : m - j = 1 := by omega
      rw [hmj] at hdvd
      have hq1 : q ≤ 1 := Nat.le_of_dvd one_pos hdvd
      have hq2 := hqpr.two_le
      omega
    · have hqle := prime_dvd_le_largestPrimeFactor hbig hqpr hdvd
      omega
  · intro a ha b hb hab
    rw [Finset.mem_coe, mem_leftRunWitness] at ha hb
    calc a = p ^ 2 * (a / p ^ 2) := (Nat.mul_div_cancel' ha.2.1).symm
      _ = p ^ 2 * (b / p ^ 2) := by rw [show a / p ^ 2 = b / p ^ 2 from hab]
      _ = b := Nat.mul_div_cancel' hb.2.1

end JSP314
