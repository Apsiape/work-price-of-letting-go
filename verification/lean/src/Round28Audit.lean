import Blueprint
import CacheState
import CacheResetConservation
import CacheAssemblyTolerances
import CachePhysicalDefect
import CacheDefectBounds
import CacheProtocol
import PhaseShellBlocks
import FinitePhaseShell
import PhaseVectorDistance
import PhaseLatticeBox
import PhaseShellColumns
import PhaseEntropyLimit
import PhaseTensorVectors
import PhaseSinePacket
import PhaseReferenceBound
import PhaseProductOverlap
import PhaseProductVectors
import PhasePureTensor
import PhaseGateDilation
import PhaseLocalPlacement
import PhasePacketDensity
import PhaseShiftPacket
import PhaseGateColumn
import PhaseHardware
import PhaseGateAccuracy
import PhaseSpectralTransport
import PhaseLocalHamiltonian
import PhaseHistoryTelescope
import PhaseDensityTensor
import PhaseHardwareEnergy
import PhaseReturnStability
import PhasePacketMap
import PhasePayloadSplit
import PhaseSpectralLabels
import PhaseEnergyRefund
import PhaseSpectralHardware
import PhaseMixedHistory
import PhaseControllerRefund
import PhaseToleranceChoice
import PhaseHandoffContinuity
import PhaseStockContinuity
import PhaseEntropyRefund
import PhaseReturnTensor
import PhaseProductReindex
import PhaseSpectralAccuracy
import PhaseBudgetEntropy
import PhaseHardwareComparison
import PhaseHardwareHistory
import PhaseHardwareReadouts
import PhaseHardwareReturn
import PhasePacketReference
import PhasePayloadHamiltonian
import PhaseSpectralData
import PhaseBudgetAssembly
import PhaseBudgetPhysical
import PhaseGlobalHamiltonian
import PhaseOperationalFrame
import PhasePacketMixed
import PhasePlacedChannel
import PhaseProtocol
import PhaseSpectralConservation
import PhaseSpectralOperational
#check @ScheduleLaw.Blueprint.cacheState
#print axioms ScheduleLaw.Blueprint.cacheState
#check @ScheduleLaw.Blueprint.cache_density
#print axioms ScheduleLaw.Blueprint.cache_density
#check @ScheduleLaw.Blueprint.CachePhysicalHamiltonian.unframe
#print axioms ScheduleLaw.Blueprint.CachePhysicalHamiltonian.unframe
#check @ScheduleLaw.Blueprint.CachePhysicalHamiltonian.resetFrame
#print axioms ScheduleLaw.Blueprint.CachePhysicalHamiltonian.resetFrame
#check @ScheduleLaw.Blueprint.CachePhysicalHamiltonian.packed_resetFrame
#print axioms ScheduleLaw.Blueprint.CachePhysicalHamiltonian.packed_resetFrame
#check @ScheduleLaw.Blueprint.CachePhysicalHamiltonian.reset_resetFrame
#print axioms ScheduleLaw.Blueprint.CachePhysicalHamiltonian.reset_resetFrame
#check @ScheduleLaw.Blueprint.CachePhysicalHamiltonian.terminal_transport
#print axioms ScheduleLaw.Blueprint.CachePhysicalHamiltonian.terminal_transport
#check @ScheduleLaw.Blueprint.CachePhysicalHamiltonian.reset_conserves
#print axioms ScheduleLaw.Blueprint.CachePhysicalHamiltonian.reset_conserves
#check @ScheduleLaw.Blueprint.CacheAssemblyTolerances.entropy_cutoff
#print axioms ScheduleLaw.Blueprint.CacheAssemblyTolerances.entropy_cutoff
#check @ScheduleLaw.Blueprint.CacheAssemblyTolerances.factory_failure
#print axioms ScheduleLaw.Blueprint.CacheAssemblyTolerances.factory_failure
#check @ScheduleLaw.Blueprint.CacheAssemblyTolerances.eventually_all
#print axioms ScheduleLaw.Blueprint.CacheAssemblyTolerances.eventually_all
#check @ScheduleLaw.Blueprint.CachePhysicalDefect.preparation_energy
#print axioms ScheduleLaw.Blueprint.CachePhysicalDefect.preparation_energy
#check @ScheduleLaw.Blueprint.CachePhysicalDefect.exact_ledger
#print axioms ScheduleLaw.Blueprint.CachePhysicalDefect.exact_ledger
#check @ScheduleLaw.Blueprint.CacheDefectBounds.source_difference
#print axioms ScheduleLaw.Blueprint.CacheDefectBounds.source_difference
#check @ScheduleLaw.Blueprint.CacheDefectBounds.ideal_source
#print axioms ScheduleLaw.Blueprint.CacheDefectBounds.ideal_source
#check @ScheduleLaw.Blueprint.CacheDefectBounds.prepared_difference
#print axioms ScheduleLaw.Blueprint.CacheDefectBounds.prepared_difference
#check @ScheduleLaw.Blueprint.CacheDefectBounds.service_error
#print axioms ScheduleLaw.Blueprint.CacheDefectBounds.service_error
#check @ScheduleLaw.Blueprint.CacheDefectBounds.defect_bound
#print axioms ScheduleLaw.Blueprint.CacheDefectBounds.defect_bound
#check @ScheduleLaw.Blueprint.CacheProtocol.realizes
#print axioms ScheduleLaw.Blueprint.CacheProtocol.realizes
#check @ScheduleLaw.Blueprint.PhaseShellBlocks.block_unitary
#print axioms ScheduleLaw.Blueprint.PhaseShellBlocks.block_unitary
#check @ScheduleLaw.Blueprint.PhaseShellBlocks.block_conserves
#print axioms ScheduleLaw.Blueprint.PhaseShellBlocks.block_conserves
#check @ScheduleLaw.Blueprint.PhaseShellBlocks.transport
#print axioms ScheduleLaw.Blueprint.PhaseShellBlocks.transport
#check @ScheduleLaw.Blueprint.FinitePhaseShell.State
#print axioms ScheduleLaw.Blueprint.FinitePhaseShell.State
#check @ScheduleLaw.Blueprint.FinitePhaseShell.shells
#print axioms ScheduleLaw.Blueprint.FinitePhaseShell.shells
#check @ScheduleLaw.Blueprint.FinitePhaseShell.Shell
#print axioms ScheduleLaw.Blueprint.FinitePhaseShell.Shell
#check @ScheduleLaw.Blueprint.FinitePhaseShell.tag
#print axioms ScheduleLaw.Blueprint.FinitePhaseShell.tag
#check @ScheduleLaw.Blueprint.FinitePhaseShell.Fiber
#print axioms ScheduleLaw.Blueprint.FinitePhaseShell.Fiber
#check @ScheduleLaw.Blueprint.FinitePhaseShell.Complete
#print axioms ScheduleLaw.Blueprint.FinitePhaseShell.Complete
#check @ScheduleLaw.Blueprint.FinitePhaseShell.fiberEquiv
#print axioms ScheduleLaw.Blueprint.FinitePhaseShell.fiberEquiv
#check @ScheduleLaw.Blueprint.FinitePhaseShell.block
#print axioms ScheduleLaw.Blueprint.FinitePhaseShell.block
#check @ScheduleLaw.Blueprint.FinitePhaseShell.frame
#print axioms ScheduleLaw.Blueprint.FinitePhaseShell.frame
#check @ScheduleLaw.Blueprint.FinitePhaseShell.gate
#print axioms ScheduleLaw.Blueprint.FinitePhaseShell.gate
#check @ScheduleLaw.Blueprint.FinitePhaseShell.block_unitary
#print axioms ScheduleLaw.Blueprint.FinitePhaseShell.block_unitary
#check @ScheduleLaw.Blueprint.FinitePhaseShell.unitary
#print axioms ScheduleLaw.Blueprint.FinitePhaseShell.unitary
#check @ScheduleLaw.Blueprint.FinitePhaseShell.conserving
#print axioms ScheduleLaw.Blueprint.FinitePhaseShell.conserving
#check @ScheduleLaw.Blueprint.FinitePhaseShell.frame_fiber
#print axioms ScheduleLaw.Blueprint.FinitePhaseShell.frame_fiber
#check @ScheduleLaw.Blueprint.FinitePhaseShell.complete_action
#print axioms ScheduleLaw.Blueprint.FinitePhaseShell.complete_action
#check @ScheduleLaw.Blueprint.PhaseVectorDistance.vector
#print axioms ScheduleLaw.Blueprint.PhaseVectorDistance.vector
#check @ScheduleLaw.Blueprint.PhaseVectorDistance.norm_unitary
#print axioms ScheduleLaw.Blueprint.PhaseVectorDistance.norm_unitary
#check @ScheduleLaw.Blueprint.PhaseVectorDistance.unitary_instances
#print axioms ScheduleLaw.Blueprint.PhaseVectorDistance.unitary_instances
#check @ScheduleLaw.Blueprint.PhaseVectorDistance.outer
#print axioms ScheduleLaw.Blueprint.PhaseVectorDistance.outer
#check @ScheduleLaw.Blueprint.PhaseVectorDistance.outer_bound
#print axioms ScheduleLaw.Blueprint.PhaseVectorDistance.outer_bound
#check @ScheduleLaw.Blueprint.PhaseVectorDistance.pure_distance
#print axioms ScheduleLaw.Blueprint.PhaseVectorDistance.pure_distance
#check @ScheduleLaw.Blueprint.PhaseVectorDistance.normalized_sum
#print axioms ScheduleLaw.Blueprint.PhaseVectorDistance.normalized_sum
#check @ScheduleLaw.Blueprint.PhaseVectorDistance.pure_entropy
#print axioms ScheduleLaw.Blueprint.PhaseVectorDistance.pure_entropy
#check @ScheduleLaw.Blueprint.PhaseLatticeBox.Lattice
#print axioms ScheduleLaw.Blueprint.PhaseLatticeBox.Lattice
#check @ScheduleLaw.Blueprint.PhaseLatticeBox.box
#print axioms ScheduleLaw.Blueprint.PhaseLatticeBox.box
#check @ScheduleLaw.Blueprint.PhaseLatticeBox.label
#print axioms ScheduleLaw.Blueprint.PhaseLatticeBox.label
#check @ScheduleLaw.Blueprint.PhaseLatticeBox.frequency
#print axioms ScheduleLaw.Blueprint.PhaseLatticeBox.frequency
#check @ScheduleLaw.Blueprint.PhaseLatticeBox.frequency_label
#print axioms ScheduleLaw.Blueprint.PhaseLatticeBox.frequency_label
#check @ScheduleLaw.Blueprint.PhaseLatticeBox.box_mem
#print axioms ScheduleLaw.Blueprint.PhaseLatticeBox.box_mem
#check @ScheduleLaw.Blueprint.PhaseLatticeBox.boxFrame
#print axioms ScheduleLaw.Blueprint.PhaseLatticeBox.boxFrame
#check @ScheduleLaw.Blueprint.PhaseLatticeBox.box_card
#print axioms ScheduleLaw.Blueprint.PhaseLatticeBox.box_card
#check @ScheduleLaw.Blueprint.PhaseLatticeBox.complete_of_interior
#print axioms ScheduleLaw.Blueprint.PhaseLatticeBox.complete_of_interior
#check @ScheduleLaw.Blueprint.PhaseShellColumns.distinct_shells
#print axioms ScheduleLaw.Blueprint.PhaseShellColumns.distinct_shells
#check @ScheduleLaw.Blueprint.PhaseShellColumns.complete_column
#print axioms ScheduleLaw.Blueprint.PhaseShellColumns.complete_column
#check @ScheduleLaw.Blueprint.PhaseEntropyLimit.log_padding
#print axioms ScheduleLaw.Blueprint.PhaseEntropyLimit.log_padding
#check @ScheduleLaw.Blueprint.PhaseEntropyLimit.modulus
#print axioms ScheduleLaw.Blueprint.PhaseEntropyLimit.modulus
#check @ScheduleLaw.Blueprint.PhaseEntropyLimit.vanishes
#print axioms ScheduleLaw.Blueprint.PhaseEntropyLimit.vanishes
#check @ScheduleLaw.Blueprint.PhaseTensorVectors.tensor
#print axioms ScheduleLaw.Blueprint.PhaseTensorVectors.tensor
#check @ScheduleLaw.Blueprint.PhaseTensorVectors.tensor_norm
#print axioms ScheduleLaw.Blueprint.PhaseTensorVectors.tensor_norm
#check @ScheduleLaw.Blueprint.PhaseTensorVectors.tensor_difference
#print axioms ScheduleLaw.Blueprint.PhaseTensorVectors.tensor_difference
#check @ScheduleLaw.Blueprint.PhaseSinePacket.box_sum
#print axioms ScheduleLaw.Blueprint.PhaseSinePacket.box_sum
#check @ScheduleLaw.Blueprint.PhaseSinePacket.scalar
#print axioms ScheduleLaw.Blueprint.PhaseSinePacket.scalar
#check @ScheduleLaw.Blueprint.PhaseSinePacket.outside_zero
#print axioms ScheduleLaw.Blueprint.PhaseSinePacket.outside_zero
#check @ScheduleLaw.Blueprint.PhaseSinePacket.scalar_norm
#print axioms ScheduleLaw.Blueprint.PhaseSinePacket.scalar_norm
#check @ScheduleLaw.Blueprint.PhaseSinePacket.scalar_difference
#print axioms ScheduleLaw.Blueprint.PhaseSinePacket.scalar_difference
#check @ScheduleLaw.Blueprint.PhaseReferenceBound.vector_matrix_norm
#print axioms ScheduleLaw.Blueprint.PhaseReferenceBound.vector_matrix_norm
#check @ScheduleLaw.Blueprint.PhaseReferenceBound.column_bound
#print axioms ScheduleLaw.Blueprint.PhaseReferenceBound.column_bound
#check @ScheduleLaw.Blueprint.PhaseReferenceBound.uniform_reference
#print axioms ScheduleLaw.Blueprint.PhaseReferenceBound.uniform_reference
#check @ScheduleLaw.Blueprint.PhaseProductOverlap.overlap_bounds
#print axioms ScheduleLaw.Blueprint.PhaseProductOverlap.overlap_bounds
#check @ScheduleLaw.Blueprint.PhaseProductOverlap.product_gap
#print axioms ScheduleLaw.Blueprint.PhaseProductOverlap.product_gap
#check @ScheduleLaw.Blueprint.PhaseProductOverlap.norm_reindex
#print axioms ScheduleLaw.Blueprint.PhaseProductOverlap.norm_reindex
#check @ScheduleLaw.Blueprint.PhaseProductVectors.product
#print axioms ScheduleLaw.Blueprint.PhaseProductVectors.product
#check @ScheduleLaw.Blueprint.PhaseProductVectors.square_sum
#print axioms ScheduleLaw.Blueprint.PhaseProductVectors.square_sum
#check @ScheduleLaw.Blueprint.PhaseProductVectors.cross_sum
#print axioms ScheduleLaw.Blueprint.PhaseProductVectors.cross_sum
#check @ScheduleLaw.Blueprint.PhaseProductVectors.norm_difference_square
#print axioms ScheduleLaw.Blueprint.PhaseProductVectors.norm_difference_square
#check @ScheduleLaw.Blueprint.PhaseProductVectors.norm_difference
#print axioms ScheduleLaw.Blueprint.PhaseProductVectors.norm_difference
#check @ScheduleLaw.Blueprint.PhasePureTensor.embedding
#print axioms ScheduleLaw.Blueprint.PhasePureTensor.embedding
#check @ScheduleLaw.Blueprint.PhasePureTensor.isometry
#print axioms ScheduleLaw.Blueprint.PhasePureTensor.isometry
#check @ScheduleLaw.Blueprint.PhasePureTensor.conjugation
#print axioms ScheduleLaw.Blueprint.PhasePureTensor.conjugation
#check @ScheduleLaw.Blueprint.PhasePureTensor.trace_norm
#print axioms ScheduleLaw.Blueprint.PhasePureTensor.trace_norm
#check @ScheduleLaw.Blueprint.PhasePureTensor.distance
#print axioms ScheduleLaw.Blueprint.PhasePureTensor.distance
#check @ScheduleLaw.Blueprint.PhaseGateDilation.adjoint_unitary
#print axioms ScheduleLaw.Blueprint.PhaseGateDilation.adjoint_unitary
#check @ScheduleLaw.Blueprint.PhaseGateDilation.conjugate_unitary
#print axioms ScheduleLaw.Blueprint.PhaseGateDilation.conjugate_unitary
#check @ScheduleLaw.Blueprint.PhaseGateDilation.conjugate_conserves
#print axioms ScheduleLaw.Blueprint.PhaseGateDilation.conjugate_conserves
#check @ScheduleLaw.Blueprint.PhaseGateDilation.diagonal_total
#print axioms ScheduleLaw.Blueprint.PhaseGateDilation.diagonal_total
#check @ScheduleLaw.Blueprint.PhaseGateDilation.basis
#print axioms ScheduleLaw.Blueprint.PhaseGateDilation.basis
#check @ScheduleLaw.Blueprint.PhaseGateDilation.energies
#print axioms ScheduleLaw.Blueprint.PhaseGateDilation.energies
#check @ScheduleLaw.Blueprint.PhaseGateDilation.phaseH
#print axioms ScheduleLaw.Blueprint.PhaseGateDilation.phaseH
#check @ScheduleLaw.Blueprint.PhaseGateDilation.inBasis
#print axioms ScheduleLaw.Blueprint.PhaseGateDilation.inBasis
#check @ScheduleLaw.Blueprint.PhaseGateDilation.gate
#print axioms ScheduleLaw.Blueprint.PhaseGateDilation.gate
#check @ScheduleLaw.Blueprint.PhaseGateDilation.basis_unitary
#print axioms ScheduleLaw.Blueprint.PhaseGateDilation.basis_unitary
#check @ScheduleLaw.Blueprint.PhaseGateDilation.unitary
#print axioms ScheduleLaw.Blueprint.PhaseGateDilation.unitary
#check @ScheduleLaw.Blueprint.PhaseGateDilation.conserving
#print axioms ScheduleLaw.Blueprint.PhaseGateDilation.conserving
#check @ScheduleLaw.Blueprint.PhaseLocalPlacement.frame
#print axioms ScheduleLaw.Blueprint.PhaseLocalPlacement.frame
#check @ScheduleLaw.Blueprint.PhaseLocalPlacement.gate
#print axioms ScheduleLaw.Blueprint.PhaseLocalPlacement.gate
#check @ScheduleLaw.Blueprint.PhaseLocalPlacement.unitary
#print axioms ScheduleLaw.Blueprint.PhaseLocalPlacement.unitary
#check @ScheduleLaw.Blueprint.PhaseLocalPlacement.local_on
#print axioms ScheduleLaw.Blueprint.PhaseLocalPlacement.local_on
#check @ScheduleLaw.Blueprint.PhaseLocalPlacement.conserving
#print axioms ScheduleLaw.Blueprint.PhaseLocalPlacement.conserving
#check @ScheduleLaw.Blueprint.PhasePacketDensity.scalarDensity
#print axioms ScheduleLaw.Blueprint.PhasePacketDensity.scalarDensity
#check @ScheduleLaw.Blueprint.PhasePacketDensity.packet
#print axioms ScheduleLaw.Blueprint.PhasePacketDensity.packet
#check @ScheduleLaw.Blueprint.PhasePacketDensity.density
#print axioms ScheduleLaw.Blueprint.PhasePacketDensity.density
#check @ScheduleLaw.Blueprint.PhasePacketDensity.matrix
#print axioms ScheduleLaw.Blueprint.PhasePacketDensity.matrix
#check @ScheduleLaw.Blueprint.PhasePacketDensity.normalized
#print axioms ScheduleLaw.Blueprint.PhasePacketDensity.normalized
#check @ScheduleLaw.Blueprint.PhasePacketDensity.norm
#print axioms ScheduleLaw.Blueprint.PhasePacketDensity.norm
#check @ScheduleLaw.Blueprint.PhasePacketDensity.entropy_zero
#print axioms ScheduleLaw.Blueprint.PhasePacketDensity.entropy_zero
#check @ScheduleLaw.Blueprint.PhasePacketDensity.supported_interior
#print axioms ScheduleLaw.Blueprint.PhasePacketDensity.supported_interior
#check @ScheduleLaw.Blueprint.PhaseShiftPacket.raw
#print axioms ScheduleLaw.Blueprint.PhaseShiftPacket.raw
#check @ScheduleLaw.Blueprint.PhaseShiftPacket.raw_support
#print axioms ScheduleLaw.Blueprint.PhaseShiftPacket.raw_support
#check @ScheduleLaw.Blueprint.PhaseShiftPacket.raw_outside
#print axioms ScheduleLaw.Blueprint.PhaseShiftPacket.raw_outside
#check @ScheduleLaw.Blueprint.PhaseShiftPacket.scalar_square_sum
#print axioms ScheduleLaw.Blueprint.PhaseShiftPacket.scalar_square_sum
#check @ScheduleLaw.Blueprint.PhaseShiftPacket.scalar_difference_square
#print axioms ScheduleLaw.Blueprint.PhaseShiftPacket.scalar_difference_square
#check @ScheduleLaw.Blueprint.PhaseShiftPacket.translated_difference
#print axioms ScheduleLaw.Blueprint.PhaseShiftPacket.translated_difference
#check @ScheduleLaw.Blueprint.PhaseShiftPacket.label_delta
#print axioms ScheduleLaw.Blueprint.PhaseShiftPacket.label_delta
#check @ScheduleLaw.Blueprint.PhaseGateColumn.complete_of_bounds
#print axioms ScheduleLaw.Blueprint.PhaseGateColumn.complete_of_bounds
#check @ScheduleLaw.Blueprint.PhaseGateColumn.column
#print axioms ScheduleLaw.Blueprint.PhaseGateColumn.column
#check @ScheduleLaw.Blueprint.PhaseGateColumn.column_formula
#print axioms ScheduleLaw.Blueprint.PhaseGateColumn.column_formula
#check @ScheduleLaw.Blueprint.PhaseHardware.rearrange
#print axioms ScheduleLaw.Blueprint.PhaseHardware.rearrange
#check @ScheduleLaw.Blueprint.PhaseHardware.split
#print axioms ScheduleLaw.Blueprint.PhaseHardware.split
#check @ScheduleLaw.Blueprint.PhaseHardware.split_apply
#print axioms ScheduleLaw.Blueprint.PhaseHardware.split_apply
#check @ScheduleLaw.Blueprint.PhaseHardware.controller
#print axioms ScheduleLaw.Blueprint.PhaseHardware.controller
#check @ScheduleLaw.Blueprint.PhaseHardware.HC
#print axioms ScheduleLaw.Blueprint.PhaseHardware.HC
#check @ScheduleLaw.Blueprint.PhaseHardware.phaseStock
#print axioms ScheduleLaw.Blueprint.PhaseHardware.phaseStock
#check @ScheduleLaw.Blueprint.PhaseHardware.extension
#print axioms ScheduleLaw.Blueprint.PhaseHardware.extension
#check @ScheduleLaw.Blueprint.PhaseHardware.hardware
#print axioms ScheduleLaw.Blueprint.PhaseHardware.hardware
#check @ScheduleLaw.Blueprint.PhaseHardware.capital_charged
#print axioms ScheduleLaw.Blueprint.PhaseHardware.capital_charged
#check @ScheduleLaw.Blueprint.PhaseHardware.nominal_debit
#print axioms ScheduleLaw.Blueprint.PhaseHardware.nominal_debit
#check @ScheduleLaw.Blueprint.PhaseHardware.toEngine
#print axioms ScheduleLaw.Blueprint.PhaseHardware.toEngine
#check @ScheduleLaw.Blueprint.PhaseGateAccuracy.unitary_column_square
#print axioms ScheduleLaw.Blueprint.PhaseGateAccuracy.unitary_column_square
#check @ScheduleLaw.Blueprint.PhaseGateAccuracy.errorColumn
#print axioms ScheduleLaw.Blueprint.PhaseGateAccuracy.errorColumn
#check @ScheduleLaw.Blueprint.PhaseGateAccuracy.column_error
#print axioms ScheduleLaw.Blueprint.PhaseGateAccuracy.column_error
#check @ScheduleLaw.Blueprint.PhaseGateAccuracy.errorMatrix
#print axioms ScheduleLaw.Blueprint.PhaseGateAccuracy.errorMatrix
#check @ScheduleLaw.Blueprint.PhaseGateAccuracy.arbitrary_reference
#print axioms ScheduleLaw.Blueprint.PhaseGateAccuracy.arbitrary_reference
#check @ScheduleLaw.Blueprint.PhaseSpectralTransport.conserving_back
#print axioms ScheduleLaw.Blueprint.PhaseSpectralTransport.conserving_back
#check @ScheduleLaw.Blueprint.PhaseSpectralTransport.labeled_conserving
#print axioms ScheduleLaw.Blueprint.PhaseSpectralTransport.labeled_conserving
#check @ScheduleLaw.Blueprint.PhaseLocalHamiltonian.body
#print axioms ScheduleLaw.Blueprint.PhaseLocalHamiltonian.body
#check @ScheduleLaw.Blueprint.PhaseLocalHamiltonian.body_matrix
#print axioms ScheduleLaw.Blueprint.PhaseLocalHamiltonian.body_matrix
#check @ScheduleLaw.Blueprint.PhaseLocalHamiltonian.component
#print axioms ScheduleLaw.Blueprint.PhaseLocalHamiltonian.component
#check @ScheduleLaw.Blueprint.PhaseLocalHamiltonian.component_hermitian
#print axioms ScheduleLaw.Blueprint.PhaseLocalHamiltonian.component_hermitian
#check @ScheduleLaw.Blueprint.PhaseLocalHamiltonian.restricted
#print axioms ScheduleLaw.Blueprint.PhaseLocalHamiltonian.restricted
#check @ScheduleLaw.Blueprint.PhaseLocalHamiltonian.localH
#print axioms ScheduleLaw.Blueprint.PhaseLocalHamiltonian.localH
#check @ScheduleLaw.Blueprint.PhaseLocalHamiltonian.local_matrix
#print axioms ScheduleLaw.Blueprint.PhaseLocalHamiltonian.local_matrix
#check @ScheduleLaw.Blueprint.PhaseLocalHamiltonian.owned_component
#print axioms ScheduleLaw.Blueprint.PhaseLocalHamiltonian.owned_component
#check @ScheduleLaw.Blueprint.PhaseHistoryTelescope.run
#print axioms ScheduleLaw.Blueprint.PhaseHistoryTelescope.run
#check @ScheduleLaw.Blueprint.PhaseHistoryTelescope.run_norm
#print axioms ScheduleLaw.Blueprint.PhaseHistoryTelescope.run_norm
#check @ScheduleLaw.Blueprint.PhaseHistoryTelescope.telescope
#print axioms ScheduleLaw.Blueprint.PhaseHistoryTelescope.telescope
#check @ScheduleLaw.Blueprint.PhaseHistoryTelescope.pure_history
#print axioms ScheduleLaw.Blueprint.PhaseHistoryTelescope.pure_history
#check @ScheduleLaw.Blueprint.PhaseDensityTensor.frame
#print axioms ScheduleLaw.Blueprint.PhaseDensityTensor.frame
#check @ScheduleLaw.Blueprint.PhaseDensityTensor.trace_norm_le
#print axioms ScheduleLaw.Blueprint.PhaseDensityTensor.trace_norm_le
#check @ScheduleLaw.Blueprint.PhaseDensityTensor.distance_le
#print axioms ScheduleLaw.Blueprint.PhaseDensityTensor.distance_le
#check @ScheduleLaw.Blueprint.PhaseDensityTensor.distance
#print axioms ScheduleLaw.Blueprint.PhaseDensityTensor.distance
#check @ScheduleLaw.Blueprint.PhaseHardwareEnergy.physical
#print axioms ScheduleLaw.Blueprint.PhaseHardwareEnergy.physical
#check @ScheduleLaw.Blueprint.PhaseReturnStability.distance_symm
#print axioms ScheduleLaw.Blueprint.PhaseReturnStability.distance_symm
#check @ScheduleLaw.Blueprint.PhaseReturnStability.whole_rest
#print axioms ScheduleLaw.Blueprint.PhaseReturnStability.whole_rest
#check @ScheduleLaw.Blueprint.PhasePacketMap.embed
#print axioms ScheduleLaw.Blueprint.PhasePacketMap.embed
#check @ScheduleLaw.Blueprint.PhasePacketMap.intertwine
#print axioms ScheduleLaw.Blueprint.PhasePacketMap.intertwine
#check @ScheduleLaw.Blueprint.PhasePacketMap.column_square
#print axioms ScheduleLaw.Blueprint.PhasePacketMap.column_square
#check @ScheduleLaw.Blueprint.PhasePacketMap.unitary_left
#print axioms ScheduleLaw.Blueprint.PhasePacketMap.unitary_left
#check @ScheduleLaw.Blueprint.PhasePacketMap.shell_error
#print axioms ScheduleLaw.Blueprint.PhasePacketMap.shell_error
#check @ScheduleLaw.Blueprint.PhasePayloadSplit.held_carrier
#print axioms ScheduleLaw.Blueprint.PhasePayloadSplit.held_carrier
#check @ScheduleLaw.Blueprint.PhasePayloadSplit.unheld_carrier
#print axioms ScheduleLaw.Blueprint.PhasePayloadSplit.unheld_carrier
#check @ScheduleLaw.Blueprint.PhasePayloadSplit.carrierPartition
#print axioms ScheduleLaw.Blueprint.PhasePayloadSplit.carrierPartition
#check @ScheduleLaw.Blueprint.PhasePayloadSplit.payload_carriers
#print axioms ScheduleLaw.Blueprint.PhasePayloadSplit.payload_carriers
#check @ScheduleLaw.Blueprint.PhaseSpectralLabels.Local
#print axioms ScheduleLaw.Blueprint.PhaseSpectralLabels.Local
#check @ScheduleLaw.Blueprint.PhaseSpectralLabels.Index
#print axioms ScheduleLaw.Blueprint.PhaseSpectralLabels.Index
#check @ScheduleLaw.Blueprint.PhaseSpectralLabels.hamiltonian
#print axioms ScheduleLaw.Blueprint.PhaseSpectralLabels.hamiltonian
#check @ScheduleLaw.Blueprint.PhaseSpectralLabels.weights
#print axioms ScheduleLaw.Blueprint.PhaseSpectralLabels.weights
#check @ScheduleLaw.Blueprint.PhaseSpectralLabels.labels
#print axioms ScheduleLaw.Blueprint.PhaseSpectralLabels.labels
#check @ScheduleLaw.Blueprint.PhaseSpectralLabels.ω
#print axioms ScheduleLaw.Blueprint.PhaseSpectralLabels.ω
#check @ScheduleLaw.Blueprint.PhaseSpectralLabels.label_energy
#print axioms ScheduleLaw.Blueprint.PhaseSpectralLabels.label_energy
#check @ScheduleLaw.Blueprint.PhaseSpectralLabels.labels_bounds
#print axioms ScheduleLaw.Blueprint.PhaseSpectralLabels.labels_bounds
#check @ScheduleLaw.Blueprint.PhaseSpectralLabels.Phase
#print axioms ScheduleLaw.Blueprint.PhaseSpectralLabels.Phase
#check @ScheduleLaw.Blueprint.PhaseSpectralLabels.phaseH
#print axioms ScheduleLaw.Blueprint.PhaseSpectralLabels.phaseH
#check @ScheduleLaw.Blueprint.PhaseSpectralLabels.localGate
#print axioms ScheduleLaw.Blueprint.PhaseSpectralLabels.localGate
#check @ScheduleLaw.Blueprint.PhaseSpectralLabels.localGate_unitary
#print axioms ScheduleLaw.Blueprint.PhaseSpectralLabels.localGate_unitary
#check @ScheduleLaw.Blueprint.PhaseSpectralLabels.localGate_conserving
#print axioms ScheduleLaw.Blueprint.PhaseSpectralLabels.localGate_conserving
#check @ScheduleLaw.Blueprint.PhaseEnergyRefund.conserving_defect_zero
#print axioms ScheduleLaw.Blueprint.PhaseEnergyRefund.conserving_defect_zero
#check @ScheduleLaw.Blueprint.PhaseEnergyRefund.raw
#print axioms ScheduleLaw.Blueprint.PhaseEnergyRefund.raw
#check @ScheduleLaw.Blueprint.PhaseEnergyRefund.oldBodyFinal
#print axioms ScheduleLaw.Blueprint.PhaseEnergyRefund.oldBodyFinal
#check @ScheduleLaw.Blueprint.PhaseEnergyRefund.phaseFinal
#print axioms ScheduleLaw.Blueprint.PhaseEnergyRefund.phaseFinal
#check @ScheduleLaw.Blueprint.PhaseEnergyRefund.phaseEnergyChange
#print axioms ScheduleLaw.Blueprint.PhaseEnergyRefund.phaseEnergyChange
#check @ScheduleLaw.Blueprint.PhaseEnergyRefund.state_energy
#print axioms ScheduleLaw.Blueprint.PhaseEnergyRefund.state_energy
#check @ScheduleLaw.Blueprint.PhaseEnergyRefund.source_raw
#print axioms ScheduleLaw.Blueprint.PhaseEnergyRefund.source_raw
#check @ScheduleLaw.Blueprint.PhaseEnergyRefund.source_energy
#print axioms ScheduleLaw.Blueprint.PhaseEnergyRefund.source_energy
#check @ScheduleLaw.Blueprint.PhaseEnergyRefund.exact_ledger
#print axioms ScheduleLaw.Blueprint.PhaseEnergyRefund.exact_ledger
#check @ScheduleLaw.Blueprint.PhaseSpectralHardware.D
#print axioms ScheduleLaw.Blueprint.PhaseSpectralHardware.D
#check @ScheduleLaw.Blueprint.PhaseSpectralHardware.dim_pos
#print axioms ScheduleLaw.Blueprint.PhaseSpectralHardware.dim_pos
#check @ScheduleLaw.Blueprint.PhaseSpectralHardware.frame
#print axioms ScheduleLaw.Blueprint.PhaseSpectralHardware.frame
#check @ScheduleLaw.Blueprint.PhaseSpectralHardware.G
#print axioms ScheduleLaw.Blueprint.PhaseSpectralHardware.G
#check @ScheduleLaw.Blueprint.PhaseSpectralHardware.G_unitary
#print axioms ScheduleLaw.Blueprint.PhaseSpectralHardware.G_unitary
#check @ScheduleLaw.Blueprint.PhaseSpectralHardware.G_local
#print axioms ScheduleLaw.Blueprint.PhaseSpectralHardware.G_local
#check @ScheduleLaw.Blueprint.PhaseSpectralHardware.controllerPhase
#print axioms ScheduleLaw.Blueprint.PhaseSpectralHardware.controllerPhase
#check @ScheduleLaw.Blueprint.PhaseSpectralHardware.phaseHFin
#print axioms ScheduleLaw.Blueprint.PhaseSpectralHardware.phaseHFin
#check @ScheduleLaw.Blueprint.PhaseSpectralHardware.hardware
#print axioms ScheduleLaw.Blueprint.PhaseSpectralHardware.hardware
#check @ScheduleLaw.Blueprint.PhaseSpectralHardware.capital_charged
#print axioms ScheduleLaw.Blueprint.PhaseSpectralHardware.capital_charged
#check @ScheduleLaw.Blueprint.PhaseSpectralHardware.nominal_debit
#print axioms ScheduleLaw.Blueprint.PhaseSpectralHardware.nominal_debit
#check @ScheduleLaw.Blueprint.PhaseMixedHistory.run
#print axioms ScheduleLaw.Blueprint.PhaseMixedHistory.run
#check @ScheduleLaw.Blueprint.PhaseMixedHistory.telescope
#print axioms ScheduleLaw.Blueprint.PhaseMixedHistory.telescope
#check @ScheduleLaw.Blueprint.PhaseControllerRefund.reservoirChange
#print axioms ScheduleLaw.Blueprint.PhaseControllerRefund.reservoirChange
#check @ScheduleLaw.Blueprint.PhaseControllerRefund.exact_ledger
#print axioms ScheduleLaw.Blueprint.PhaseControllerRefund.exact_ledger
#check @ScheduleLaw.Blueprint.PhaseControllerRefund.bound
#print axioms ScheduleLaw.Blueprint.PhaseControllerRefund.bound
#check @ScheduleLaw.Blueprint.PhaseToleranceChoice.inverse_vanishes
#print axioms ScheduleLaw.Blueprint.PhaseToleranceChoice.inverse_vanishes
#check @ScheduleLaw.Blueprint.PhaseToleranceChoice.eventually_all
#print axioms ScheduleLaw.Blueprint.PhaseToleranceChoice.eventually_all
#check @ScheduleLaw.Blueprint.PhaseHandoffContinuity.carrier
#print axioms ScheduleLaw.Blueprint.PhaseHandoffContinuity.carrier
#check @ScheduleLaw.Blueprint.PhaseHandoffContinuity.handoff
#print axioms ScheduleLaw.Blueprint.PhaseHandoffContinuity.handoff
#check @ScheduleLaw.Blueprint.PhaseStockContinuity.diagonalH
#print axioms ScheduleLaw.Blueprint.PhaseStockContinuity.diagonalH
#check @ScheduleLaw.Blueprint.PhaseStockContinuity.diagonal_readout
#print axioms ScheduleLaw.Blueprint.PhaseStockContinuity.diagonal_readout
#check @ScheduleLaw.Blueprint.PhaseStockContinuity.level
#print axioms ScheduleLaw.Blueprint.PhaseStockContinuity.level
#check @ScheduleLaw.Blueprint.PhaseStockContinuity.energy_sub
#print axioms ScheduleLaw.Blueprint.PhaseStockContinuity.energy_sub
#check @ScheduleLaw.Blueprint.PhaseEntropyRefund.bound
#print axioms ScheduleLaw.Blueprint.PhaseEntropyRefund.bound
#check @ScheduleLaw.Blueprint.PhaseReturnTensor.frame
#print axioms ScheduleLaw.Blueprint.PhaseReturnTensor.frame
#check @ScheduleLaw.Blueprint.PhaseReturnTensor.state
#print axioms ScheduleLaw.Blueprint.PhaseReturnTensor.state
#check @ScheduleLaw.Blueprint.PhaseReturnTensor.rest
#print axioms ScheduleLaw.Blueprint.PhaseReturnTensor.rest
#check @ScheduleLaw.Blueprint.PhaseReturnTensor.product
#print axioms ScheduleLaw.Blueprint.PhaseReturnTensor.product
#check @ScheduleLaw.Blueprint.PhaseReturnTensor.whole_rest
#print axioms ScheduleLaw.Blueprint.PhaseReturnTensor.whole_rest
#check @ScheduleLaw.Blueprint.PhaseProductReindex.rest
#print axioms ScheduleLaw.Blueprint.PhaseProductReindex.rest
#check @ScheduleLaw.Blueprint.PhaseProductReindex.product_distance
#print axioms ScheduleLaw.Blueprint.PhaseProductReindex.product_distance
#check @ScheduleLaw.Blueprint.PhaseSpectralAccuracy.error_factor
#print axioms ScheduleLaw.Blueprint.PhaseSpectralAccuracy.error_factor
#check @ScheduleLaw.Blueprint.PhaseSpectralAccuracy.error_bound
#print axioms ScheduleLaw.Blueprint.PhaseSpectralAccuracy.error_bound
#check @ScheduleLaw.Blueprint.PhaseBudgetEntropy.controllerDensity
#print axioms ScheduleLaw.Blueprint.PhaseBudgetEntropy.controllerDensity
#check @ScheduleLaw.Blueprint.PhaseBudgetEntropy.product
#print axioms ScheduleLaw.Blueprint.PhaseBudgetEntropy.product
#check @ScheduleLaw.Blueprint.PhaseBudgetEntropy.reindex
#print axioms ScheduleLaw.Blueprint.PhaseBudgetEntropy.reindex
#check @ScheduleLaw.Blueprint.PhaseBudgetEntropy.product_entropy
#print axioms ScheduleLaw.Blueprint.PhaseBudgetEntropy.product_entropy
#check @ScheduleLaw.Blueprint.PhaseBudgetEntropy.reindex_entropy
#print axioms ScheduleLaw.Blueprint.PhaseBudgetEntropy.reindex_entropy
#check @ScheduleLaw.Blueprint.PhaseBudgetEntropy.controller
#print axioms ScheduleLaw.Blueprint.PhaseBudgetEntropy.controller
#check @ScheduleLaw.Blueprint.PhaseBudgetEntropy.battery
#print axioms ScheduleLaw.Blueprint.PhaseBudgetEntropy.battery
#check @ScheduleLaw.Blueprint.PhaseHardwareComparison.Close
#print axioms ScheduleLaw.Blueprint.PhaseHardwareComparison.Close
#check @ScheduleLaw.Blueprint.PhaseHardwareComparison.observer
#print axioms ScheduleLaw.Blueprint.PhaseHardwareComparison.observer
#check @ScheduleLaw.Blueprint.PhaseHardwareComparison.service
#print axioms ScheduleLaw.Blueprint.PhaseHardwareComparison.service
#check @ScheduleLaw.Blueprint.PhaseHardwareComparison.body
#print axioms ScheduleLaw.Blueprint.PhaseHardwareComparison.body
#check @ScheduleLaw.Blueprint.PhaseHardwareComparison.controller
#print axioms ScheduleLaw.Blueprint.PhaseHardwareComparison.controller
#check @ScheduleLaw.Blueprint.PhaseHardwareComparison.rest
#print axioms ScheduleLaw.Blueprint.PhaseHardwareComparison.rest
#check @ScheduleLaw.Blueprint.PhaseHardwareComparison.battery
#print axioms ScheduleLaw.Blueprint.PhaseHardwareComparison.battery
#check @ScheduleLaw.Blueprint.PhaseHardwareComparison.reservoir
#print axioms ScheduleLaw.Blueprint.PhaseHardwareComparison.reservoir
#check @ScheduleLaw.Blueprint.PhaseHardwareHistory.from_cut_error
#print axioms ScheduleLaw.Blueprint.PhaseHardwareHistory.from_cut_error
#check @ScheduleLaw.Blueprint.PhaseHardwareReadouts.split_inverse
#print axioms ScheduleLaw.Blueprint.PhaseHardwareReadouts.split_inverse
#check @ScheduleLaw.Blueprint.PhaseHardwareReadouts.whole
#print axioms ScheduleLaw.Blueprint.PhaseHardwareReadouts.whole
#check @ScheduleLaw.Blueprint.PhaseHardwareReadouts.controller
#print axioms ScheduleLaw.Blueprint.PhaseHardwareReadouts.controller
#check @ScheduleLaw.Blueprint.PhaseHardwareReadouts.rest
#print axioms ScheduleLaw.Blueprint.PhaseHardwareReadouts.rest
#check @ScheduleLaw.Blueprint.PhaseHardwareReturn.frame
#print axioms ScheduleLaw.Blueprint.PhaseHardwareReturn.frame
#check @ScheduleLaw.Blueprint.PhaseHardwareReturn.oldShape
#print axioms ScheduleLaw.Blueprint.PhaseHardwareReturn.oldShape
#check @ScheduleLaw.Blueprint.PhaseHardwareReturn.newShape
#print axioms ScheduleLaw.Blueprint.PhaseHardwareReturn.newShape
#check @ScheduleLaw.Blueprint.PhaseHardwareReturn.tensor_shape
#print axioms ScheduleLaw.Blueprint.PhaseHardwareReturn.tensor_shape
#check @ScheduleLaw.Blueprint.PhaseHardwareReturn.controller_unpack
#print axioms ScheduleLaw.Blueprint.PhaseHardwareReturn.controller_unpack
#check @ScheduleLaw.Blueprint.PhaseHardwareReturn.idle_return
#print axioms ScheduleLaw.Blueprint.PhaseHardwareReturn.idle_return
#check @ScheduleLaw.Blueprint.PhaseHardwareReturn.stability
#print axioms ScheduleLaw.Blueprint.PhaseHardwareReturn.stability
#check @ScheduleLaw.Blueprint.PhasePacketReference.coeff
#print axioms ScheduleLaw.Blueprint.PhasePacketReference.coeff
#check @ScheduleLaw.Blueprint.PhasePacketReference.lift
#print axioms ScheduleLaw.Blueprint.PhasePacketReference.lift
#check @ScheduleLaw.Blueprint.PhasePacketReference.wires
#print axioms ScheduleLaw.Blueprint.PhasePacketReference.wires
#check @ScheduleLaw.Blueprint.PhasePacketReference.lift_norm
#print axioms ScheduleLaw.Blueprint.PhasePacketReference.lift_norm
#check @ScheduleLaw.Blueprint.PhasePacketReference.action
#print axioms ScheduleLaw.Blueprint.PhasePacketReference.action
#check @ScheduleLaw.Blueprint.PhasePacketReference.vector_error
#print axioms ScheduleLaw.Blueprint.PhasePacketReference.vector_error
#check @ScheduleLaw.Blueprint.PhasePacketReference.pure_error
#print axioms ScheduleLaw.Blueprint.PhasePacketReference.pure_error
#check @ScheduleLaw.Blueprint.PhasePayloadHamiltonian.carrier_sum
#print axioms ScheduleLaw.Blueprint.PhasePayloadHamiltonian.carrier_sum
#check @ScheduleLaw.Blueprint.PhasePayloadHamiltonian.body_part
#print axioms ScheduleLaw.Blueprint.PhasePayloadHamiltonian.body_part
#check @ScheduleLaw.Blueprint.PhasePayloadHamiltonian.total
#print axioms ScheduleLaw.Blueprint.PhasePayloadHamiltonian.total
#check @ScheduleLaw.Blueprint.PhaseSpectralData.local_card_pos
#print axioms ScheduleLaw.Blueprint.PhaseSpectralData.local_card_pos
#check @ScheduleLaw.Blueprint.PhaseSpectralData.cutConstant
#print axioms ScheduleLaw.Blueprint.PhaseSpectralData.cutConstant
#check @ScheduleLaw.Blueprint.PhaseSpectralData.constant
#print axioms ScheduleLaw.Blueprint.PhaseSpectralData.constant
#check @ScheduleLaw.Blueprint.PhaseSpectralData.cut_nonneg
#print axioms ScheduleLaw.Blueprint.PhaseSpectralData.cut_nonneg
#check @ScheduleLaw.Blueprint.PhaseSpectralData.constant_nonneg
#print axioms ScheduleLaw.Blueprint.PhaseSpectralData.constant_nonneg
#check @ScheduleLaw.Blueprint.PhaseSpectralData.cut_error
#print axioms ScheduleLaw.Blueprint.PhaseSpectralData.cut_error
#check @ScheduleLaw.Blueprint.PhaseSpectralData.dim
#print axioms ScheduleLaw.Blueprint.PhaseSpectralData.dim
#check @ScheduleLaw.Blueprint.PhaseSpectralData.controllerPhase_matrix
#print axioms ScheduleLaw.Blueprint.PhaseSpectralData.controllerPhase_matrix
#check @ScheduleLaw.Blueprint.PhaseBudgetAssembly.uniform
#print axioms ScheduleLaw.Blueprint.PhaseBudgetAssembly.uniform
#check @ScheduleLaw.Blueprint.PhaseBudgetAssembly.coefficient_bounds
#print axioms ScheduleLaw.Blueprint.PhaseBudgetAssembly.coefficient_bounds
#check @ScheduleLaw.Blueprint.PhaseBudgetAssembly.realizes
#print axioms ScheduleLaw.Blueprint.PhaseBudgetAssembly.realizes
#check @ScheduleLaw.Blueprint.PhaseBudgetPhysical.energyCoeff
#print axioms ScheduleLaw.Blueprint.PhaseBudgetPhysical.energyCoeff
#check @ScheduleLaw.Blueprint.PhaseBudgetPhysical.failureCoeff
#print axioms ScheduleLaw.Blueprint.PhaseBudgetPhysical.failureCoeff
#check @ScheduleLaw.Blueprint.PhaseBudgetPhysical.tailCoeff
#print axioms ScheduleLaw.Blueprint.PhaseBudgetPhysical.tailCoeff
#check @ScheduleLaw.Blueprint.PhaseBudgetPhysical.coefficient
#print axioms ScheduleLaw.Blueprint.PhaseBudgetPhysical.coefficient
#check @ScheduleLaw.Blueprint.PhaseBudgetPhysical.return_bound
#print axioms ScheduleLaw.Blueprint.PhaseBudgetPhysical.return_bound
#check @ScheduleLaw.Blueprint.PhaseBudgetPhysical.controller_bound
#print axioms ScheduleLaw.Blueprint.PhaseBudgetPhysical.controller_bound
#check @ScheduleLaw.Blueprint.PhaseBudgetPhysical.failure_bound
#print axioms ScheduleLaw.Blueprint.PhaseBudgetPhysical.failure_bound
#check @ScheduleLaw.Blueprint.PhaseBudgetPhysical.tail_bound
#print axioms ScheduleLaw.Blueprint.PhaseBudgetPhysical.tail_bound
#check @ScheduleLaw.Blueprint.PhaseGlobalHamiltonian.total
#print axioms ScheduleLaw.Blueprint.PhaseGlobalHamiltonian.total
#check @ScheduleLaw.Blueprint.PhaseOperationalFrame.Local
#print axioms ScheduleLaw.Blueprint.PhaseOperationalFrame.Local
#check @ScheduleLaw.Blueprint.PhaseOperationalFrame.Env
#print axioms ScheduleLaw.Blueprint.PhaseOperationalFrame.Env
#check @ScheduleLaw.Blueprint.PhaseOperationalFrame.old
#print axioms ScheduleLaw.Blueprint.PhaseOperationalFrame.old
#check @ScheduleLaw.Blueprint.PhaseOperationalFrame.global
#print axioms ScheduleLaw.Blueprint.PhaseOperationalFrame.global
#check @ScheduleLaw.Blueprint.PhaseOperationalFrame.contactFrame
#print axioms ScheduleLaw.Blueprint.PhaseOperationalFrame.contactFrame
#check @ScheduleLaw.Blueprint.PhaseOperationalFrame.factor
#print axioms ScheduleLaw.Blueprint.PhaseOperationalFrame.factor
#check @ScheduleLaw.Blueprint.PhaseOperationalFrame.device
#print axioms ScheduleLaw.Blueprint.PhaseOperationalFrame.device
#check @ScheduleLaw.Blueprint.PhaseOperationalFrame.old_device
#print axioms ScheduleLaw.Blueprint.PhaseOperationalFrame.old_device
#check @ScheduleLaw.Blueprint.PhasePacketMixed.attach
#print axioms ScheduleLaw.Blueprint.PhasePacketMixed.attach
#check @ScheduleLaw.Blueprint.PhasePacketMixed.reassoc
#print axioms ScheduleLaw.Blueprint.PhasePacketMixed.reassoc
#check @ScheduleLaw.Blueprint.PhasePacketMixed.reduce_lift
#print axioms ScheduleLaw.Blueprint.PhasePacketMixed.reduce_lift
#check @ScheduleLaw.Blueprint.PhasePacketMixed.gate_reindex
#print axioms ScheduleLaw.Blueprint.PhasePacketMixed.gate_reindex
#check @ScheduleLaw.Blueprint.PhasePacketMixed.output_reduces
#print axioms ScheduleLaw.Blueprint.PhasePacketMixed.output_reduces
#check @ScheduleLaw.Blueprint.PhasePacketMixed.attach_evolve
#print axioms ScheduleLaw.Blueprint.PhasePacketMixed.attach_evolve
#check @ScheduleLaw.Blueprint.PhasePacketMixed.channel
#print axioms ScheduleLaw.Blueprint.PhasePacketMixed.channel
#check @ScheduleLaw.Blueprint.PhasePlacedChannel.channel
#print axioms ScheduleLaw.Blueprint.PhasePlacedChannel.channel
#check @ScheduleLaw.Blueprint.PhaseProtocol.realizes
#print axioms ScheduleLaw.Blueprint.PhaseProtocol.realizes
#check @ScheduleLaw.Blueprint.PhaseSpectralConservation.body_energy
#print axioms ScheduleLaw.Blueprint.PhaseSpectralConservation.body_energy
#check @ScheduleLaw.Blueprint.PhaseSpectralConservation.conserving
#print axioms ScheduleLaw.Blueprint.PhaseSpectralConservation.conserving
#check @ScheduleLaw.Blueprint.PhaseSpectralConservation.engine
#print axioms ScheduleLaw.Blueprint.PhaseSpectralConservation.engine
#check @ScheduleLaw.Blueprint.PhaseSpectralConservation.engine_hardware
#print axioms ScheduleLaw.Blueprint.PhaseSpectralConservation.engine_hardware
#check @ScheduleLaw.Blueprint.PhaseSpectralOperational.idle
#print axioms ScheduleLaw.Blueprint.PhaseSpectralOperational.idle
#check @ScheduleLaw.Blueprint.PhaseSpectralOperational.wires
#print axioms ScheduleLaw.Blueprint.PhaseSpectralOperational.wires
#check @ScheduleLaw.Blueprint.PhaseSpectralOperational.ideal
#print axioms ScheduleLaw.Blueprint.PhaseSpectralOperational.ideal
#check @ScheduleLaw.Blueprint.PhaseSpectralOperational.idle_run
#print axioms ScheduleLaw.Blueprint.PhaseSpectralOperational.idle_run
#check @ScheduleLaw.Blueprint.PhaseSpectralOperational.old_device
#print axioms ScheduleLaw.Blueprint.PhaseSpectralOperational.old_device
#check @ScheduleLaw.Blueprint.PhaseSpectralOperational.actual_device
#print axioms ScheduleLaw.Blueprint.PhaseSpectralOperational.actual_device
#check @ScheduleLaw.Blueprint.PhaseSpectralOperational.idle_device
#print axioms ScheduleLaw.Blueprint.PhaseSpectralOperational.idle_device
#check @ScheduleLaw.Blueprint.PhaseSpectralOperational.ideal_evolve
#print axioms ScheduleLaw.Blueprint.PhaseSpectralOperational.ideal_evolve
#check @ScheduleLaw.Blueprint.PhaseSpectralOperational.device_error
#print axioms ScheduleLaw.Blueprint.PhaseSpectralOperational.device_error
#check @ScheduleLaw.Blueprint.PhaseSpectralOperational.joint_cut
#print axioms ScheduleLaw.Blueprint.PhaseSpectralOperational.joint_cut
#check @ScheduleLaw.Blueprint.PhaseSpectralOperational.close
#print axioms ScheduleLaw.Blueprint.PhaseSpectralOperational.close
#print axioms ScheduleLaw.Blueprint.finite_factory_of_small_residue_coding
#print axioms ScheduleLaw.Blueprint.source_factory_circuits
#print axioms ScheduleLaw.Blueprint.cyclic_cache_protocol
#print axioms ScheduleLaw.Blueprint.finite_conserving_phase
#print axioms ScheduleLaw.Blueprint.corrected_joint_tangent
#print axioms ScheduleLaw.Blueprint.pointwise_physical_compiler
#print axioms ScheduleLaw.Blueprint.work_law_for_schedules
