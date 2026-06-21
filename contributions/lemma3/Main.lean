def StrictlyIncreasingOn (D : DenseLinearOrderNoEndpoints R) (I : Set (Power R 1))
    (B : Set (Power R 1)) (f : {x : Power R 1 // I x} -> {y : Power R 1 // B y}) : Prop :=
  forall (x y : Power R 1) (hx : I x) (hy : I y), Lt1 D x y -> Lt1 D (f ⟨x, hx⟩).1 (f ⟨y, hy⟩).1

def StrictlyDecreasingOn (D : DenseLinearOrderNoEndpoints R) (I : Set (Power R 1))
    (B : Set (Power R 1)) (f : {x : Power R 1 // I x} -> {y : Power R 1 // B y}) : Prop :=
  forall (x y : Power R 1) (hx : I x) (hy : I y), Lt1 D x y -> Lt1 D (f ⟨y, hy⟩).1 (f ⟨x, hx⟩).1

def StrictlyMonotoneOn (D : DenseLinearOrderNoEndpoints R) (I : Set (Power R 1))
    (B : Set (Power R 1)) (f : {x : Power R 1 // I x} -> {y : Power R 1 // B y}) : Prop :=
  StrictlyIncreasingOn D I B f \/ StrictlyDecreasingOn D I B f

lemma injective_of_strictly_monotone_on {R : Type u} (D : DenseLinearOrderNoEndpoints R)
    {I B : Set (Power R 1)} (f : {x : Power R 1 // I x} -> {y : Power R 1 // B y})
    (hmono : StrictlyMonotoneOn D I B f) : f.Injective := by
    intro x y h_eq
    by_contra h_ne
    have h_coord_ne : Not (x.val.coord1 = y.val.coord1) := by
      intro h
      apply h_ne
      ext i
      fin_cases i
      exact h
    rcases D.trichotomy x.val.coord1 y.val.coord1 with ⟨hlt, -⟩ | ⟨heq, -⟩ | ⟨hlt, -⟩
    · rcases hmono with hinc | hdec <;> apply D.irrefl
      · simpa [h_eq] using hinc x.val y.val x.2 y.2 hlt
      · simpa [h_eq] using hdec x.val y.val x.2 y.2 hlt
    · exact h_coord_ne heq
    · rcases hmono with hinc | hdec <;> apply D.irrefl
      · simpa [h_eq] using hinc y.val x.val y.2 x.2 hlt
      · simpa [h_eq] using hdec y.val x.val y.2 x.2 hlt

lemma IsInfinite1.image_of_injective {R : Type u}
    {A B : Set (Power R 1)} (f : {x : Power R 1 // A x} -> {y : Power R 1 // B y})
    (hinj : f.Injective) (hA : IsInfinite1 A) :
    IsInfinite1 (FunctionImage (m := 1) (n := 1) (A := A) (B := B) f) := by
  intro hFin
  apply hA
  rcases hFin with ⟨L, hL⟩
  have h_pre (r : R) (hr : L.Mem r) : exists y : A, (f y).val = fun _ => r :=
    let ⟨y, hy, heq⟩ := (hL (fun _ => r)).mpr (by simpa [Power.coord1, hr])
    ⟨⟨y, hy⟩, heq.symm⟩
  choose p hp using h_pre
  refine ⟨L.attach.map fun ⟨r, hr⟩ => (p r hr).val.coord1, fun y => ⟨fun hy => ?_, fun hc => ?_⟩⟩
  · have hrL : L.Mem ((f ⟨y, hy⟩).val.coord1) := (hL (f ⟨y, hy⟩).val).mp ⟨y, hy, rfl⟩
    have hpre : p _ hrL = ⟨y, hy⟩ :=
      hinj (Subtype.ext (by rw [hp _ hrL]; ext i; fin_cases i; rw [Power.coord1]; rfl))
    exact List.mem_map.mpr ⟨⟨_, hrL⟩, L.mem_attach _, by simp [hpre]⟩
  · obtain ⟨⟨r, hr⟩, -, heq⟩ := List.mem_map.mp hc
    rw [show y = (p r hr).val by ext i; fin_cases i; exact heq.symm]
    exact (p r hr).property

lemma exists_two_points_in_open_interval (D : DenseLinearOrderNoEndpoints R) [Nonempty R]
    (a b : Endpoint R) (hab : Endpoint.lt D a b) :
    exists r s : R,
      D.lt r s /\
      openInterval D a b (fun _ => r) /\
      openInterval D a b (fun _ => s) /\
      forall x : Power R 1,
        openInterval D (Endpoint.finite r) (Endpoint.finite s) x ->
        openInterval D a b x := by
  rcases a with (a_neg | a_fin | a_pos)
  · rcases b with (b_neg | b_fin | b_pos)
    · exfalso
      exact hab
    · obtain ⟨p, hp⟩ := D.no_left_endpoint b_fin
      obtain ⟨r, _, hr_b⟩ := D.dense hp
      obtain ⟨s, hrs, hs_b⟩ := D.dense hr_b
      refine ⟨r, s, hrs, ⟨trivial, hr_b⟩, ⟨trivial, hs_b⟩, fun x ⟨_, hx⟩ => ⟨trivial, D.trans hx hs_b⟩⟩
    · obtain ⟨x0⟩ : Nonempty R := inferInstance
      obtain ⟨r, _⟩ := D.no_right_endpoint x0
      obtain ⟨s, hrs⟩ := D.no_right_endpoint r
      refine ⟨r, s, hrs, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, fun _ _ => ⟨trivial, trivial⟩⟩
  · rcases b with (b_neg | b_fin | b_pos)
    · exfalso
      exact hab
    · obtain ⟨r, har, hrb⟩ := D.dense hab
      obtain ⟨s, hrs, hsb⟩ := D.dense hrb
      refine ⟨r, s, hrs, ⟨har, hrb⟩, ⟨D.trans har hrs, hsb⟩, fun x ⟨hx1, hx2⟩ =>
        ⟨D.trans har hx1, D.trans hx2 hsb⟩⟩
    · obtain ⟨r, har⟩ := D.no_right_endpoint a_fin
      obtain ⟨s, hrs⟩ := D.no_right_endpoint r
      refine ⟨r, s, hrs, ⟨har, trivial⟩, ⟨D.trans har hrs, trivial⟩, fun x ⟨hx, _⟩ =>
        ⟨D.trans har hx, trivial⟩⟩
  · exfalso
    exact hab

lemma nonempty_of_isInfinite1 {A : Set (Power R 1)} (h : IsInfinite1 A) : Nonempty R := by
  by_contra hne
  haveI : IsEmpty R := not_nonempty_iff.mp hne
  exact h ⟨[], fun x => ⟨isEmptyElim (x 0), fun h => by cases h⟩⟩

lemma exists_order_preserving_bijection_interval
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (hmono : StrictlyMonotoneOn D I B f.toFun)
    {c d : Power R 1} (hc : I c) (hd : I d)
    {r s : R} (hrs : D.lt r s)
    (hcr : (f.toFun ⟨c, hc⟩).1 = (fun _ => r))
    (hds : (f.toFun ⟨d, hd⟩).1 = (fun _ => s))
    (hValueInterval : (openInterval D (Endpoint.finite r) (Endpoint.finite s)).Subset
      (FunctionImage (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) :
    exists a b : Endpoint R,
      Endpoint.lt D a b /\
      (openInterval D a b).Subset I /\
      (forall x, openInterval D a b x ->
        exists hx : I x,
          openInterval D (Endpoint.finite r) (Endpoint.finite s) (f.toFun ⟨x, hx⟩).1) /\
      (forall y, openInterval D (Endpoint.finite r) (Endpoint.finite s) y ->
        exists x, openInterval D a b x /\
          exists hx : I x, (f.toFun ⟨x, hx⟩).1 = y) := by
  sorry

lemma continuous_of_interval_bijection
    (M : OMinimalStructure D) {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    {a b : Endpoint R} (hab : Endpoint.lt D a b)
    (hDomain : (openInterval D a b).Subset I)
    {r s : R} (hrs : D.lt r s)
    (hMapsTo : forall x, openInterval D a b x ->
        exists hx : I x,
          openInterval D (Endpoint.finite r) (Endpoint.finite s) (f.toFun ⟨x, hx⟩).1)
    (hSurj : forall y, openInterval D (Endpoint.finite r) (Endpoint.finite s) y ->
        exists x, openInterval D a b x /\
          exists hx : I x, (f.toFun ⟨x, hx⟩).1 = y) :
    (openInterval D a b).Subset
      (ContinuousPoints D I
        (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) := by
  sorry

theorem strictly_monotone_definable_continuous_on_subinterval
    (M : OMinimalStructure D)
    {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (hmono : StrictlyMonotoneOn D I B f.toFun)
    (hInf : IsInfinite1 I) :
    exists a b : Endpoint R,
      Endpoint.lt D a b /\
      (openInterval D a b).Subset I /\
      (openInterval D a b).Subset (ContinuousPoints D I
        (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) := by
  have hinj : f.toFun.Injective := injective_of_strictly_monotone_on D f.toFun hmono
  let fIm := FunctionImage (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
  have hImageInf : IsInfinite1 fIm := hInf.image_of_injective f.toFun hinj
  have hFImDef : M.S 1 fIm := functionImage_mem M f
  have hFImFin : FiniteUnionOfPointsAndIntervals D fIm := (M.ominimal fIm).mp hFImDef
  obtain ⟨a0, b0, hab0, hSubJ⟩ := infinite_contains_interval D fIm hFImFin hImageInf
  haveI : Nonempty R := nonempty_of_isInfinite1 hInf
  obtain ⟨r, s, hrs, hrJ, hsJ, hSubRS⟩ := exists_two_points_in_open_interval D a0 b0 hab0
  have hValueInterval : (openInterval D (Endpoint.finite r) (Endpoint.finite s)).Subset fIm :=
    fun x hx => hSubJ x (hSubRS x hx)
  have hIm_r : exists c : Power R 1, exists hc : I c, (f.toFun ⟨c, hc⟩).val = fun _ => r := by
    have hmem := hSubJ (fun _ => r) hrJ
    simpa [fIm, FunctionImage, eq_comm] using hmem
  obtain ⟨c, hc, hcr⟩ := hIm_r
  have hIm_s : exists d : Power R 1, exists hd : I d, (f.toFun ⟨d, hd⟩).val = fun _ => s := by
    have hmem := hSubJ (fun _ => s) hsJ
    simpa [fIm, FunctionImage, eq_comm] using hmem
  obtain ⟨d, hd, hds⟩ := hIm_s
  obtain ⟨a, b, hab, hDomain, hMapsTo, hSurj⟩ :=
    exists_order_preserving_bijection_interval M f hmono hc hd hrs hcr hds hValueInterval
  have hCont := continuous_of_interval_bijection M f hab hDomain hrs hMapsTo hSurj
  exact ⟨a, b, hab, hDomain, hCont⟩
