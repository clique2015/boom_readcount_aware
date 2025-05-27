//******************************************************************************
// Copyright (c) 2015 - 2018, The Regents of the University of California (Regents).
// All Rights Reserved. See LICENSE and LICENSE.SiFive for license details.
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
// RISCV Processor Issue Logic
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------

package boom.v3.exu

import chisel3._
import chisel3.util._

import org.chipsalliance.cde.config.Parameters
import freechips.rocketchip.util.Str

import FUConstants._
import boom.v3.common._

/**
 * Specific type of issue unit
 *
 * @param params issue queue params
 * @param numWakeupPorts number of wakeup ports for the issue queue
 */

 // Module for finding max readcount
 /**
class MaxSelector(val size: Int, val width: Int) extends Module {
  val io = IO(new Bundle {
    val in  = Input(Vec(size, UInt(width.W)))
    val max = Output(UInt(width.W))
  })

  for (i <- 0 until size) {
 //   printf(p"MaxSelector input[$i] = ${io.in(i)}\n")
  }

  io.max := io.in.reduce((a, b) => Mux(a > b, a, b))
 // printf(p"MaxSelector output max = ${io.max}\n")
}
**/
// Module for finding k-th max readcount (where k = issueWidth)

class MaxSelector(val size: Int, val width: Int, val k: Int) extends Module {
  require(k >= 1 && k <= size, s"k ($k) must be in range [1, $size]")

  val io = IO(new Bundle {
    val in  = Input(Vec(size, UInt(width.W)))
    val max = Output(UInt(width.W))
  })

  // Use an array of wires per "iteration" to simulate mutation
  val stages = Array.fill(size + 1)(Wire(Vec(size, UInt(width.W))))

  // Stage 0 is the initial input
  stages(0) := io.in

  for (i <- 0 until size) {
    for (j <- 0 until size) {
      stages(i + 1)(j) := stages(i)(j)
    }

    for (j <- 0 until size - 1 - i) {
      when (stages(i)(j) < stages(i)(j + 1)) {
        stages(i + 1)(j) := stages(i)(j + 1)
        stages(i + 1)(j + 1) := stages(i)(j)
      }
    }
  }

  // Output the k-th max from the final sorted stage
  io.max := stages(size)(k - 1)
}
class IssueUnitStatic(
  params: IssueParams,
  numWakeupPorts: Int)
  (implicit p: Parameters)
  extends IssueUnit(params.numEntries, params.issueWidth, numWakeupPorts, params.iqType, params.dispatchWidth)
{
  //-------------------------------------------------------------
  // Issue Table

  val entry_wen_oh = WireInit(VecInit(Seq.fill(numIssueSlots)(0.U(dispatchWidth.W))))
  for (i <- 0 until numIssueSlots) {
    issue_slots(i).in_uop.valid := entry_wen_oh(i).orR
    issue_slots(i).in_uop.bits  := Mux1H(entry_wen_oh(i), dis_uops)
    issue_slots(i).clear        := false.B
  }

  //-------------------------------------------------------------
  // Dispatch/Entry Logic
  // find a slot to enter a new dispatched instruction

  val entry_wen_oh_array = Array.fill(numIssueSlots,dispatchWidth){false.B}
  var allocated = VecInit(Seq.fill(dispatchWidth){false.B}) // did an instruction find an issue width?

  for (i <- 0 until numIssueSlots) {
    var next_allocated = Wire(Vec(dispatchWidth, Bool()))
    var can_allocate = !(issue_slots(i).valid)

    for (w <- 0 until dispatchWidth) {
      entry_wen_oh_array(i)(w) = can_allocate && !(allocated(w))

      next_allocated(w) := can_allocate | allocated(w)
      can_allocate = can_allocate && allocated(w)
    }

    allocated = next_allocated
  }

  // if we can find an issue slot, do we actually need it?
  // also, translate from Scala data structures to Chisel Vecs
  for (i <- 0 until numIssueSlots) {
    val temp_uop_val = Wire(Vec(dispatchWidth, Bool()))

    for (w <- 0 until dispatchWidth) {
      // TODO add ctrl bit for "allocates iss_slot"
      temp_uop_val(w) := io.dis_uops(w).valid &&
                         !dis_uops(w).exception &&
                         !dis_uops(w).is_fence &&
                         !dis_uops(w).is_fencei &&
                         entry_wen_oh_array(i)(w)
    }
    entry_wen_oh(i) := temp_uop_val.asUInt
  }

  for (w <- 0 until dispatchWidth) {
    io.dis_uops(w).ready := allocated(w)
  }

  //-------------------------------------------------------------
  // Issue Select Logic

  for (w <- 0 until issueWidth) {
    io.iss_valids(w) := false.B
    io.iss_uops(w)   := NullMicroOp
    // unsure if this is overkill
    io.iss_uops(w).prs1 := 0.U
    io.iss_uops(w).prs2 := 0.U
    io.iss_uops(w).prs3 := 0.U
    io.iss_uops(w).lrs1_rtype := RT_X
    io.iss_uops(w).lrs2_rtype := RT_X
  }





  // TODO can we use flatten to get an array of bools on issue_slot(*).request?
  val lo_request_not_satisfied = Array.fill(numIssueSlots){Bool()}
  val hi_request_not_satisfied = Array.fill(numIssueSlots){Bool()}



  for (i <- 0 until numIssueSlots) {
    lo_request_not_satisfied(i) = issue_slots(i).request
    hi_request_not_satisfied(i) = issue_slots(i).request_hp
    issue_slots(i).grant := false.B // default
   // printf(p"lo_request => ${lo_request_not_satisfied(i)}, hi_request=>${lo_request_not_satisfied(i)} \n")
    //printf(p"slot_request => ${issue_slots(i).request}, slot_request_hp=>${issue_slots(i).request_hp} \n")
}


  for (w <- 0 until issueWidth) {
    var port_issued = false.B

    // Wires to track readcounts and eligibility
  val readcounts = Wire(Vec(numIssueSlots, UInt(4.W)))
  val mask       = Wire(Vec(numIssueSlots, Bool()))

  val readcountsl = Wire(Vec(numIssueSlots, UInt(4.W)))
  val maskl       = Wire(Vec(numIssueSlots, Bool()))

  // Instantiate MaxSelector
  val maxSelector = Module(new MaxSelector(numIssueSlots, 4, issueWidth))
  maxSelector.io.in := readcounts
  val max_readcount = maxSelector.io.max


  val maxSelectorl = Module(new MaxSelector(numIssueSlots, 4, issueWidth))
  maxSelectorl.io.in := readcountsl
  val max_readcountl = maxSelectorl.io.max

     //printf(p"Issuing slot at index ${selected_idx}, uop=${io.iss_uops(w)}\n")
    // first look for high priority requests
    for (i <- 0 until numIssueSlots) {
      val can_allocate = (issue_slots(i).uop.fu_code & io.fu_types(w)) =/= 0.U
      mask(i) := hi_request_not_satisfied(i) && can_allocate
      readcounts(i) := Mux(mask(i), issue_slots(i).uop.readcount, 0.U)

     // printf(p"hi_request_not_satisfied ${hi_request_not_satisfied(i)}: can_allocate=$can_allocate,  cond=$cond, readcount=${readcounts(i)}\n")
      
    }
    for (i <- 0 until numIssueSlots) {
      val can_allocate = (issue_slots(i).uop.fu_code & io.fu_types(w)) =/= 0.U
      val issuedHi = Wire(Bool())
      issuedHi := false.B
      // Issue the instruction
      when (mask(i) && (issue_slots(i).uop.readcount >= max_readcount) && !port_issued) {
      //  when (mask(i) && !port_issued) { 
  //    printf(p"max_readcount => ${max_readcount}, issue_slotsuopreadcount=>${issue_slots(i).uop.readcount} \n")
        issue_slots(i).grant := true.B
        io.iss_valids(w)     := true.B
        io.iss_uops(w)       := issue_slots(i).uop
        issuedHi             := true.B
      }

      val port_already_in_use     = port_issued
      port_issued                 = (hi_request_not_satisfied(i) && can_allocate 
      && (issue_slots(i).uop.readcount >= max_readcount)) | port_issued
      // deassert lo_request if hi_request is 1.
      lo_request_not_satisfied(i) = (lo_request_not_satisfied(i) && !hi_request_not_satisfied(i))
      // if request is 0, stay 0. only stay 1 if request is true and can't allocate
      hi_request_not_satisfied(i) = (hi_request_not_satisfied(i) 
      && (!issuedHi || !can_allocate || port_already_in_use))
    }    


     // now look for low priority requests
    for (i <- 0 until numIssueSlots) {
      val can_allocate = (issue_slots(i).uop.fu_code & io.fu_types(w)) =/= 0.U
            maskl(i) := lo_request_not_satisfied(i) && can_allocate
      readcountsl(i) := Mux(maskl(i), issue_slots(i).uop.readcount, 0.U)
    }


      
    for (i <- 0 until numIssueSlots) {
      val can_allocate = (issue_slots(i).uop.fu_code & io.fu_types(w)) =/= 0.U
      val issuedLo = Wire(Bool())
      issuedLo := false.B
      when (maskl(i)&& !port_issued && (issue_slots(i).uop.readcount >= max_readcountl)) {
     //  printf(p"max_readcountl => ${max_readcountl}, issue_slotsuopreadcount=>${issue_slots(i).uop.readcount} \n") 
        issue_slots(i).grant := true.B
        io.iss_valids(w)     := true.B
        io.iss_uops(w)       := issue_slots(i).uop
        issuedLo             := true.B
      }

      val port_already_in_use     = port_issued
      port_issued                 = (lo_request_not_satisfied(i) && can_allocate && (issue_slots(i).uop.readcount >= max_readcountl)) | port_issued
      // if request is 0, stay 0. only stay 1 if request is true and can't allocate or port already in use
      lo_request_not_satisfied(i) = (lo_request_not_satisfied(i) && ((!issuedLo && can_allocate) || !can_allocate || port_already_in_use))
    }
  }
}
