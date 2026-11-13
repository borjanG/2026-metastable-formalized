import Metastability.SourceMain
import Metastability.NormalizedStageCenters
import Metastability.SourcePilot
import Metastability.StoppedEnergy
import Metastability.GeneralClock
import Metastability.BlockGeometry
import Metastability.CapDistances
import Metastability.GeodesicBarycenter
import Metastability.FiniteTransport
import Metastability.EnergyAssembly
import Metastability.CapInvariance
import Metastability.TightGeometry
import Metastability.TerminalEnergy
import Metastability.BlockContraction
import Metastability.TreeCapEnlargement
import Metastability.InitialPreparation
import Metastability.ActiveCollisionTiming
import Metastability.SourceTerminalTiming
import Metastability.TerminalParentGeometry
import Metastability.PlateauCollision
import Metastability.StageRestart

/-!
Checked production entry point for the metastability formalization.
`Metastability.SourceMain.main_and_cascade` proves the joint general USA/SA
source theorem: deterministic centers, uniform energy and finite empirical
transport limits, and quantitative collision windows with the same shift and
actual cutoff clock. `NormalizedStageCenters` additionally proves literal
normalized-mean barycenter propagation on produced stage intervals.
The two-particle pilot and all earlier source/analytic components remain
imported. The historical unapproved declaration packet in `audit/` is not
imported or designated a frozen statement. The finite angular coupling cost
is not identified here with a separate measure-library Wasserstein object.
All production modules are dependencies of these imports.
-/
