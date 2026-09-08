# Proof graphs

One diagram per problem: the benchmark theorem at the top, and the helper lemmas
LeanFlow's orchestrator proposed beneath it. An arrow `A --> B` means **A depends
on B**, so the leaves are the lemmas proved first and the root is the published
benchmark statement.

These are the graphs as actually built and proved, taken from each run's
`DAG.json`. Rounded nodes are helper lemmas; the doubled node is the benchmark
theorem.


## PB-Basic-025 — Geometry, IMO-easy

*folklore* · 6 nodes · 114 API calls · 16 min

```mermaid
flowchart TD
    n_n_4ef1149c1f317418[["PBBasic025"]]
    n_H_segment("pbbasic025_segmentPlacement")
    n_H_heights("pbbasic025_heightProducts")
    n_H_incenter("pbbasic025_incenterDisplacement")
    n_H_algebra("pbbasic025_innerProductCancellation")
    n_H_spans("pbbasic025_angleOfOrthogonalSpans")
    n_n_4ef1149c1f317418 --> n_H_segment
    n_n_4ef1149c1f317418 --> n_H_incenter
    n_n_4ef1149c1f317418 --> n_H_algebra
    n_n_4ef1149c1f317418 --> n_H_spans
    n_H_incenter --> n_H_heights
```

## PB-Basic-026 — Geometry, IMO-medium

*Novel Problem* · 8 nodes · 199 API calls · 27 min

```mermaid
flowchart TD
    n_n_dcaea2aaca9454db[["PBBasic026"]]
    n_pb026_contact_frame("PBBasic026_contact_frame")
    n_pb026_apex_model("PBBasic026_apex_model")
    n_pb026_circle_model("PBBasic026_circle_model")
    n_pb026_reflection_model("PBBasic026_reflection_model")
    n_pb026_circumcenter_model("PBBasic026_circumcenter_model")
    n_pb026_affine_certificate("PBBasic026_affine_certificate")
    n_pb026_one_side("PBBasic026_one_side")
    n_n_dcaea2aaca9454db --> n_pb026_one_side
    n_pb026_one_side --> n_pb026_contact_frame
    n_pb026_one_side --> n_pb026_apex_model
    n_pb026_one_side --> n_pb026_circle_model
    n_pb026_one_side --> n_pb026_reflection_model
    n_pb026_one_side --> n_pb026_circumcenter_model
    n_pb026_one_side --> n_pb026_affine_certificate
```

## PB-Basic-028 — Geometry, IMO-medium

*Novel Problem* · 7 nodes · 175 API calls · 27 min

```mermaid
flowchart TD
    n_n_de60bd0f96b953cd[["PBBasic028"]]
    n_pb028_normalized_frame("normalizedFrame")
    n_pb028_inside_two_line_tangency("insideTwoLineTangency")
    n_pb028_midpoint_circle_invariants("midpointCircleInvariants")
    n_pb028_select_small_tangency_root("selectSmallTangencyRoot")
    n_pb028_altitude_foot_vectors("altitudeFootVectors")
    n_pb028_unit_ray_triangle_incenter("unitRayTriangleIncenter")
    n_n_de60bd0f96b953cd --> n_pb028_normalized_frame
    n_n_de60bd0f96b953cd --> n_pb028_inside_two_line_tangency
    n_n_de60bd0f96b953cd --> n_pb028_midpoint_circle_invariants
    n_n_de60bd0f96b953cd --> n_pb028_select_small_tangency_root
    n_n_de60bd0f96b953cd --> n_pb028_altitude_foot_vectors
    n_n_de60bd0f96b953cd --> n_pb028_unit_ray_triangle_incenter
```

## PB-Basic-029 — Geometry, IMO-medium

*(modified) IMO Shortlist 2008 G5* · 2 nodes · 162 API calls · 57 min

```mermaid
flowchart TD
    n_n_80f14e29c0a4fbe4[["PBBasic029"]]
    n_n_pbb029_pairs("pair_count")
    n_n_80f14e29c0a4fbe4 --> n_n_pbb029_pairs
```

## PB-Basic-030 — Geometry, IMO-easy

*Novel Problem* · 2 nodes · 169 API calls · 97 min

```mermaid
flowchart TD
    n_n_a38f8c6ecb5656c2[["PBBasic030"]]
    n_n_pb030_discriminant_swap("discriminantSwap")
    n_n_a38f8c6ecb5656c2 --> n_n_pb030_discriminant_swap
```

## PB-Advanced-002 — Combinatorics, IMO-medium

*Novel Problem* · 10 nodes · 106 API calls · 21 min

```mermaid
flowchart TD
    n_n_9607dd58fd026180[["PBAdvanced002"]]
    n_pb002_short_image_iterate("short_image_iterate")
    n_pb002_cycle_witnesses("cycle_witnesses")
    n_pb002_small_common_multiple_120("small_common_multiple_120")
    n_pb002_long_iterate_visits_cycle("long_iterate_visits_cycle")
    n_pb002_lift_mutual_reachability("lift_mutual_reachability")
    n_pb002_long_iterate_pumpable("long_iterate_pumpable")
    n_pb002_period_of_pumping("period_of_pumping")
    n_pb002_comparable_family_common_orbit("comparable_family_common_orbit")
    n_pb002_eventual_period_configuration_bound("eventual_period_configuration_bound")
    n_n_9607dd58fd026180 --> n_pb002_cycle_witnesses
    n_n_9607dd58fd026180 --> n_pb002_small_common_multiple_120
    n_n_9607dd58fd026180 --> n_pb002_long_iterate_pumpable
    n_n_9607dd58fd026180 --> n_pb002_period_of_pumping
    n_n_9607dd58fd026180 --> n_pb002_eventual_period_configuration_bound
    n_pb002_cycle_witnesses --> n_pb002_short_image_iterate
    n_pb002_long_iterate_pumpable --> n_pb002_short_image_iterate
    n_pb002_long_iterate_pumpable --> n_pb002_long_iterate_visits_cycle
    n_pb002_long_iterate_pumpable --> n_pb002_lift_mutual_reachability
    n_pb002_eventual_period_configuration_bound --> n_pb002_comparable_family_common_orbit
```

## PB-Advanced-003 — Geometry, IMO-hard

*Novel Problem* · 5 nodes · 674 API calls · 221 min

```mermaid
flowchart TD
    n_n_d4430223390a3731[["PBAdvanced003"]]
    n_pb003_scalar_data("scalarData")
    n_pb003_forward_bisector("forwardBisectorOfInternalTangency")
    n_pb003_coefficient_collinearity("cyclicCoefficientCollinearity")
    n_pb003_negative_power_secant("negativePowerCoaxialSecant")
    n_n_d4430223390a3731 --> n_pb003_scalar_data
    n_n_d4430223390a3731 --> n_pb003_forward_bisector
    n_n_d4430223390a3731 --> n_pb003_coefficient_collinearity
    n_n_d4430223390a3731 --> n_pb003_negative_power_secant
```

## PB-Advanced-004 — Combinatorics, IMO-easy

*Novel Problem* · 5 nodes · 88 API calls · 18 min

```mermaid
flowchart TD
    n_n_cd373c1e5327fa07[["PBAdvanced004"]]
    n_pb004_edge_sides("PB004_edge_side_structure")
    n_pb004_edge_side_branches("PB004_edge_side_branches")
    n_pb004_threshold_separator("PB004_threshold_separator")
    n_pb004_nested_cuts("PB004_nested_edge_cuts")
    n_n_cd373c1e5327fa07 --> n_pb004_edge_sides
    n_n_cd373c1e5327fa07 --> n_pb004_threshold_separator
    n_n_cd373c1e5327fa07 --> n_pb004_nested_cuts
    n_pb004_edge_side_branches --> n_pb004_edge_sides
    n_pb004_threshold_separator --> n_pb004_edge_sides
    n_pb004_threshold_separator --> n_pb004_edge_side_branches
    n_pb004_nested_cuts --> n_pb004_edge_sides
```

## PB-Advanced-005 — Geometry, IMO-medium

*Novel Problem* · 6 nodes · 105 API calls · 24 min

```mermaid
flowchart TD
    n_n_072b85ab6afd3a75[["PBAdvanced005"]]
    n_n_pb005_sector_coordinates("sectorCoordinates")
    n_n_pb005_positive_cone_interior("positiveConeInterior")
    n_n_pb005_oblique_gram("obliqueGramIdentity")
    n_n_pb005_intercept_branch("admissibleInterceptBranch")
    n_n_pb005_partner_transfer("partnerInterceptTransfer")
    n_n_072b85ab6afd3a75 --> n_n_pb005_sector_coordinates
    n_n_072b85ab6afd3a75 --> n_n_pb005_positive_cone_interior
    n_n_072b85ab6afd3a75 --> n_n_pb005_oblique_gram
    n_n_072b85ab6afd3a75 --> n_n_pb005_intercept_branch
    n_n_072b85ab6afd3a75 --> n_n_pb005_partner_transfer
```

## PB-Advanced-009 — Geometry, IMO-hard

*Novel Problem* · 1 nodes · 200 API calls · 84 min

```mermaid
flowchart TD
    n_n_e0caa4cadc463672[["PBAdvanced009"]]
```

## PB-Advanced-010 — Geometry, IMO-medium

*Novel Problem* · 8 nodes · 158 API calls · 44 min

```mermaid
flowchart TD
    n_n_d50306ee1c65b130[["PBAdvanced010"]]
    n_pb010_frame("normalizedFrame")
    n_pb010_cospherical_coordinates("cosphericalCoordinateQuadratic")
    n_pb010_euler_parameters("eulerParameters")
    n_pb010_oblique_interpolation("obliqueInterpolation")
    n_pb010_equal_power("equalPower")
    n_pb010_radical_axis("radicalAxisDet")
    n_pb010_secant_locus("secantLocus")
    n_n_d50306ee1c65b130 --> n_pb010_frame
    n_n_d50306ee1c65b130 --> n_pb010_cospherical_coordinates
    n_n_d50306ee1c65b130 --> n_pb010_euler_parameters
    n_n_d50306ee1c65b130 --> n_pb010_equal_power
    n_n_d50306ee1c65b130 --> n_pb010_radical_axis
    n_n_d50306ee1c65b130 --> n_pb010_secant_locus
    n_pb010_equal_power --> n_pb010_oblique_interpolation
```

## PB-Advanced-015 — Geometry, IMO-hard

*Novel Problem* · 10 nodes · 323 API calls · 53 min

```mermaid
flowchart TD
    n_n_a3ef6b7bd7842923[["PBAdvanced015"]]
    n_pb015_normalize("pb015_normalize")
    n_pb015_tangent_line_sq("pb015_tangent_line_sq")
    n_pb015_orthic_equations("pb015_orthic_equations")
    n_pb015_tangency_relation("pb015_tangency_relation")
    n_pb015_circumcircle_coordinates("pb015_circumcircle_coordinates")
    n_pb015_secant_coordinates("pb015_secant_coordinates")
    n_pb015_internal_bisector("pb015_internal_bisector")
    n_pb015_external_parameter("pb015_external_parameter")
    n_pb015_coordinate_collinear("pb015_coordinate_collinear")
    n_n_a3ef6b7bd7842923 --> n_pb015_normalize
    n_n_a3ef6b7bd7842923 --> n_pb015_tangent_line_sq
    n_n_a3ef6b7bd7842923 --> n_pb015_orthic_equations
    n_n_a3ef6b7bd7842923 --> n_pb015_tangency_relation
    n_n_a3ef6b7bd7842923 --> n_pb015_circumcircle_coordinates
    n_n_a3ef6b7bd7842923 --> n_pb015_secant_coordinates
    n_n_a3ef6b7bd7842923 --> n_pb015_internal_bisector
    n_n_a3ef6b7bd7842923 --> n_pb015_external_parameter
    n_n_a3ef6b7bd7842923 --> n_pb015_coordinate_collinear
```

## PB-Advanced-016 — Geometry, IMO-easy

*Novel Problem* · 7 nodes · 202 API calls · 35 min

```mermaid
flowchart TD
    n_n_02150cf1fee8e5bd[["PBAdvanced016"]]
    n_pb016_side_weights("incenter_side_weights")
    n_pb016_weighted_frame("weighted_frame")
    n_pb016_initial_coordinates("initial_coordinates")
    n_pb016_weighted_circle("weighted_circle_equation")
    n_pb016_second_intersection("second_intersection")
    n_pb016_crossed_lines("crossed_lines")
    n_n_02150cf1fee8e5bd --> n_pb016_weighted_frame
    n_n_02150cf1fee8e5bd --> n_pb016_initial_coordinates
    n_n_02150cf1fee8e5bd --> n_pb016_weighted_circle
    n_n_02150cf1fee8e5bd --> n_pb016_second_intersection
    n_n_02150cf1fee8e5bd --> n_pb016_crossed_lines
    n_pb016_weighted_frame --> n_pb016_side_weights
```

## PB-Advanced-018 — Combinatorics, IMO-hard

*Novel Problem* · 9 nodes · 446 API calls · 94 min

```mermaid
flowchart TD
    n_n_ceaa36276e0a462f[["PBAdvanced018"]]
    n_pb018_grid_cover("grid_cover")
    n_pb018_no_mono_path("no_mono_path")
    n_pb018_pack124("pack124")
    n_pb018_confinement("confinement")
    n_pb018_rectangle_atoms("rectangle_atoms")
    n_pb018_parameters("parameters")
    n_pb018_small_certificates("small_certificates")
    n_pb018_countercoloring("countercoloring")
    n_n_ceaa36276e0a462f --> n_pb018_no_mono_path
    n_n_ceaa36276e0a462f --> n_pb018_countercoloring
    n_pb018_no_mono_path --> n_pb018_grid_cover
    n_pb018_countercoloring --> n_pb018_pack124
    n_pb018_countercoloring --> n_pb018_confinement
    n_pb018_countercoloring --> n_pb018_rectangle_atoms
    n_pb018_countercoloring --> n_pb018_parameters
    n_pb018_countercoloring --> n_pb018_small_certificates
```

## PB-Advanced-021 — Combinatorics, IMO-hard

*(Modified) IMO 2024 P3* · 12 nodes · 149 API calls · 28 min

```mermaid
flowchart TD
    n_n_c0e80a364d3119e0[["PBAdvanced021"]]
    n_n_pb021_occurrence_edges("pb021_occurrence_successors_strict")
    n_n_pb021_no_large_large("pb021_no_large_large")
    n_n_pb021_alternating_tail("pb021_eventual_small_large_alternation")
    n_n_pb021_large_rank_count("pb021_large_occurrence_rank_count")
    n_n_pb021_rank_representation("pb021_eventual_rank_representation")
    n_n_pb021_sorted_increment("pb021_sorted_increment_identity")
    n_n_pb021_sorted_prefix("pb021_sorted_prefix_dominance")
    n_n_pb021_defect_data("pb021_rank_walk_defect_data")
    n_n_pb021_bounded_width("pb021_rank_walk_bounded_width_of_defect")
    n_n_pb021_bounded_periodicity("pb021_bounded_rank_walk_eventually_periodic")
    n_n_pb021_rank_periodicity("pb021_rank_walk_eventually_periodic")
    n_n_c0e80a364d3119e0 --> n_n_pb021_rank_representation
    n_n_c0e80a364d3119e0 --> n_n_pb021_rank_periodicity
    n_n_pb021_no_large_large --> n_n_pb021_occurrence_edges
    n_n_pb021_alternating_tail --> n_n_pb021_occurrence_edges
    n_n_pb021_alternating_tail --> n_n_pb021_no_large_large
    n_n_pb021_large_rank_count --> n_n_pb021_no_large_large
    n_n_pb021_rank_representation --> n_n_pb021_alternating_tail
    n_n_pb021_rank_representation --> n_n_pb021_large_rank_count
    n_n_pb021_defect_data --> n_n_pb021_sorted_increment
    n_n_pb021_defect_data --> n_n_pb021_sorted_prefix
    n_n_pb021_bounded_width --> n_n_pb021_sorted_increment
    n_n_pb021_bounded_width --> n_n_pb021_sorted_prefix
    n_n_pb021_rank_periodicity --> n_n_pb021_defect_data
    n_n_pb021_rank_periodicity --> n_n_pb021_sorted_prefix
    n_n_pb021_rank_periodicity --> n_n_pb021_bounded_width
    n_n_pb021_rank_periodicity --> n_n_pb021_bounded_periodicity
```

## PB-Advanced-022 — Geometry, IMO-easy

*(Modified) IMO 2024 P4* · 8 nodes · 229 API calls · 30 min

```mermaid
flowchart TD
    n_n_f98b3205dff1d1bc[["PBAdvanced022"]]
    n_pb022_cartesian_frame("cartesianFrame")
    n_pb022_incenter_coordinates("incenterCoordinates")
    n_pb022_side_parameters("sideParameters")
    n_pb022_tangent_normal_square("tangentNormalSquare")
    n_pb022_negative_arc_point("negativeArcPoint")
    n_pb022_dot_det_algebra("dotDetAlgebra")
    n_pb022_supplement_criterion("supplementCriterion")
    n_n_f98b3205dff1d1bc --> n_pb022_cartesian_frame
    n_n_f98b3205dff1d1bc --> n_pb022_incenter_coordinates
    n_n_f98b3205dff1d1bc --> n_pb022_side_parameters
    n_n_f98b3205dff1d1bc --> n_pb022_tangent_normal_square
    n_n_f98b3205dff1d1bc --> n_pb022_negative_arc_point
    n_n_f98b3205dff1d1bc --> n_pb022_dot_det_algebra
    n_n_f98b3205dff1d1bc --> n_pb022_supplement_criterion
```

## PB-Advanced-023 — Combinatorics, IMO-medium

*(Modified) IMO 2024 P5* · 7 nodes · 147 API calls · 31 min

```mermaid
flowchart TD
    n_n_81f5458e7fff2c5c[["PBAdvanced023"]]
    n_pb023_grid_crossing("gridCrossing")
    n_pb023_selection_extension("selectionExtension")
    n_pb023_two_path_adversary("twoPathAdversary")
    n_pb023_row_two_sweep("rowTwoSweep")
    n_pb023_interior_routes("interiorRoutes")
    n_pb023_boundary_recovery("boundaryRecovery")
    n_n_81f5458e7fff2c5c --> n_pb023_two_path_adversary
    n_n_81f5458e7fff2c5c --> n_pb023_row_two_sweep
    n_n_81f5458e7fff2c5c --> n_pb023_interior_routes
    n_n_81f5458e7fff2c5c --> n_pb023_boundary_recovery
    n_pb023_two_path_adversary --> n_pb023_grid_crossing
    n_pb023_two_path_adversary --> n_pb023_selection_extension
```

## PB-Advanced-027 — Combinatorics, IMO-hard

*USAMO 2025* · 6 nodes · 62 API calls · 15 min

```mermaid
flowchart TD
    n_n_1213c8589c793899[["PBAdvanced027"]]
    n_n_pb027_similarity_dist_sq("similarity_dist_sq")
    n_n_pb027_normalize_pair("normalize_pair")
    n_n_pb027_exterior_iff("exterior_iff")
    n_n_pb027_potential_connectivity("potential_connectivity")
    n_n_pb027_crossing_obstruction("crossing_obstruction")
    n_n_1213c8589c793899 --> n_n_pb027_exterior_iff
    n_n_1213c8589c793899 --> n_n_pb027_potential_connectivity
    n_n_1213c8589c793899 --> n_n_pb027_crossing_obstruction
    n_n_pb027_exterior_iff --> n_n_pb027_similarity_dist_sq
    n_n_pb027_exterior_iff --> n_n_pb027_normalize_pair
```
