import LeanFlowProofs.PBBasic026AffineCertificate
import LeanFlowProofs.PBBasic026ApexModel
import LeanFlowProofs.PBBasic026CircleModel
import LeanFlowProofs.PBBasic026CircumcenterModel
import LeanFlowProofs.PBBasic026ContactFrame
import LeanFlowProofs.PBBasic026ReflectionModel
import Mathlib

theorem LeanFlowProofs.PBBasic026_one_side
    (s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2)
    (W : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)))
    (X : EuclideanSpace ℝ (Fin 2))
    (hB : s.points 1 ∈ W) (hC : s.points 2 ∈ W)
    (ht : (Affine.Simplex.insphere s).IsIntTangentAt W X) :
    let I := Affine.Simplex.incenter s
    let O := Affine.Simplex.circumcenter s
    let r := Affine.Simplex.inradius s
    let R := dist O (s.points 0)
    let D := Affine.Simplex.touchpoint s ∅ 0
    let D' := EuclideanGeometry.reflection (affineSpan ℝ {s.points 0, I}) D
    I - (r / (3 * R)) • (O - I) ∈ affineSpan ℝ {D', X} := by 
  rcases PBBasic026_contact_frame s with ⟨hr, u, v, m, n, hu, hv, huv, hm, hn, hD, h1, h2, hA⟩
  have hab : s.insphere.IsTangent (affineSpan ℝ {s.points 0, s.points 1}) := by
    have h := (s.isTangentAt_insphere_touchpoint 2).isTangent
    have he : ({(2 : Fin 3)}ᶜ : Set (Fin 3)) = {0, 1} := by ext i; fin_cases i <;> simp
    simpa [Affine.Simplex.range_faceOpposite_points, he, Set.image_insert_eq] using h
  have hac : s.insphere.IsTangent (affineSpan ℝ {s.points 0, s.points 2}) := by
    have h := (s.isTangentAt_insphere_touchpoint 1).isTangent
    have he : ({(1 : Fin 3)}ᶜ : Set (Fin 3)) = {0, 2} := by ext i; fin_cases i <;> simp
    simpa [Affine.Simplex.range_faceOpposite_points, he, Set.image_insert_eq] using h
  rw [h1] at hab
  rw [h2] at hac
  obtain ⟨hk, ha⟩ := PBBasic026_apex_model s.insphere (s.points 0) u v m n hr hu hv huv hm hn hA hab hac
  have hx := PBBasic026_circle_model s.insphere W X u v m n hr hu hv huv hm hn (h1 ▸ hB) (h2 ▸ hC) ht
  have hd := PBBasic026_reflection_model s.incenter u v s.inradius (n-m) (m*n) hr hk hu hv huv
  have ho := PBBasic026_circumcenter_model s.incenter s.circumcenter u v s.inradius m n hr hm hn hk hu hv huv
  have hc := PBBasic026_affine_certificate u v (n-m) (m*n) hk
  dsimp only at ha hx hd ho hc
  have he01 : dist s.circumcenter (s.points 0) = dist s.circumcenter (s.points 1) := by
    simp [dist_comm, s.dist_circumcenter_eq_circumradius]
  have he12 : dist s.circumcenter (s.points 1) = dist s.circumcenter (s.points 2) := by
    simp [dist_comm, s.dist_circumcenter_eq_circumradius]
  rw [ha, h1] at he01
  rw [h1, h2] at he12
  obtain ⟨ho, hR⟩ := ho he01 he12
  let rho := ((n-m)^2 + (m*n+1)^2) / (4*(m*n-1))
  let beta := 2*((n-m)^2+(m*n)^2) / (3*((n-m)^2+m*n*(m*n+1)))
  let o := ((n-m)/2) • u + (rho-(m*n+1)/2) • v
  let d := (2*(n-m)*(m*n+1)/((n-m)^2+(m*n+1)^2)) • u +
    (((n-m)^2-(m*n+1)^2)/((n-m)^2+(m*n+1)^2)) • v
  let x := (-2*(m*n)*(n-m)/((n-m)^2+(m*n)^2)) • u +
    (((m*n)^2-(n-m)^2)/((n-m)^2+(m*n)^2)) • v
  change (-(1/(3*rho))) • o = (1-beta) • d + beta • x at hc
  change s.circumcenter = s.incenter + s.inradius • o at ho
  change X = s.incenter + s.inradius • x at hx
  change _ = s.incenter + s.inradius • d at hd
  have hR' : dist s.circumcenter (s.points 0) = s.inradius * rho := by
    rw [ha]; exact hR
  dsimp only
  change s.points 0 = s.incenter + s.inradius • _ at ha
  rw [hR', hD, ha, hd, hx, ho, add_sub_cancel_left]
  have hs : s.inradius / (3 * (s.inradius * rho)) = 1 / (3*rho) := by
    field_simp
    <;> ring
  rw [hs]
  have he : s.incenter - (1/(3*rho)) • (s.inradius • o) =
      AffineMap.lineMap (s.incenter + s.inradius • d) (s.incenter + s.inradius • x) beta := by
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    calc
      _ = s.incenter + s.inradius • ((-(1/(3*rho))) • o) := by module
      _ = _ := by rw [hc]; module
  rw [he]
  exact AffineMap.lineMap_mem_affineSpan_pair beta (s.incenter + s.inradius • d) (s.incenter + s.inradius • x)

