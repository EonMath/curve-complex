import Unbranched

namespace AlternatingSphereCover
open CurveComplex

noncomputable def actualBranchedDoubleCover : BranchedDoubleCover Total Sphere where
  projection := projection
  projection_continuous := projection_continuous
  projection_surjective := projection_surjective
  deck := deckHomeomorph
  deck_involution := deck_involution
  branch := branchFinset
  branch_card := branchFinset_card
  fixed_iff_branch := by
    intro x
    exact (fixed_iff_branch x).trans (mem_branchFinset _).symm
  projection_deck := projection_deck
  fiber_pair := fiber_pair
  unbranched_cover := unbranched_cover
  branch_chart := by
    intro x hx
    exact Classical.choice (exists_squareBranchChart x ((mem_branchFinset _).mp hx))

end AlternatingSphereCover
