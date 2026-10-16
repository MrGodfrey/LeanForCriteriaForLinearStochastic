# Adapted MathFin sources

The CommonItoIsometry, CommonItoL2, CommonItoCLM, CommonItoProcess,
CommonItoProcessMartingale, CommonItoProcessGeneral, CommonItoCross,
CommonItoContinuous, CommonItoContinuousVersion, CommonItoPredictable,
CommonDriftPredictable and CommonDriftModification modules
retain Raphael Coelho’s copyright and Apache-2.0 license. Their pinned source is
formal-applied-math/formal-mathfin at 99b836298731c432a6242fdb6cb51c1c97f37902.
The license is reproduced in MathFin-APACHE-2.0.txt. Local adaptation notices in
each source describe the specified common filtration and cross-channel changes.
The source checkout under .lake/packages/MathFin is unchanged.

CommonItoPredictable adapts ItoProcessPredictable; CommonDriftPredictable
adapts DriftProcessPredictable; CommonDriftModification adapts
DriftProcessModification. Each retains the upstream copyright header.
These adaptations use the given common filtration and the locally proved
integral operators; the public release binds each adapted source by its SHA-256 in
../audit/claims.en.json and ../audit/release-manifest.json.

FiniteExponentialTotality adapts the finite signed-measure/Laplace argument of
WienerExponentialTotality. CommonStepProcess adapts stepSP and the finite sum
lemma of ItoIntegralBrownian. CommonItoLocality adapts the past-factor locality
proofs of ItoIntegralLocality to the specified common filtration, reusing the
upstream generic bounded multiplication operator. These three files retain the
upstream Apache-2.0 copyright. Each adapted source is bound by its SHA-256 in the public release inventory
and manifest. The formalization guide describes the scope of the source review.
