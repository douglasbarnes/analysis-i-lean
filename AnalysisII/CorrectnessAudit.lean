import AnalysisII.CoreTheorems

/-!
# Analysis II compiled correctness-audit surface

This file deliberately lists every course-facing declaration currently carrying an
`AnalysisII.sourceNNN_...` name.  It is not a completeness certificate: the companion
`check_analysis_ii_correctness.py` script compares these declaration IDs with the 68
source theorem-like environments and reports missing and partial coverage.

Source 49 (compact-domain Heine--Cantor) is intentionally covered by the more general
`source010_heineCantor` declaration.
-/

namespace AnalysisII.CorrectnessAudit

#check AnalysisII.source001_uniformCauchySeqOn_of_tendstoUniformly
#check AnalysisII.source001_tendstoUniformly_of_uniformCauchySeqOn
#check AnalysisII.source002_uniform_limit_continuous
#check AnalysisII.source010_heineCantor
#check AnalysisII.source028_metric_ball_open
#check AnalysisII.source039_limit_unique
#check AnalysisII.source041_iUnion_open
#check AnalysisII.source041_inter_open
#check AnalysisII.source043_iInter_closed
#check AnalysisII.source043_union_closed
#check AnalysisII.source044_finite_closed
#check AnalysisII.source052_contraction_unique_fixedPoint
#check AnalysisII.source052_fixedPoint_of_contracting_iterate
#check AnalysisII.source054_fderiv_unique
#check AnalysisII.source055_fderiv_continuous
#check AnalysisII.source055_continuousLinearMap_derivative
#check AnalysisII.source057_apply_le_opNorm
#check AnalysisII.source059_chain_rule

end AnalysisII.CorrectnessAudit
