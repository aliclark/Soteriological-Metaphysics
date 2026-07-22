/-
================================================================================
  WeldAndArrow.Doctrines.Ledger
  Productivity-ledger register, reception commands, and the purge face
================================================================================

This module records the checked face of the ledger case. The neutral machinery
states that landings inherit the call modality of the receiving function; the
case model then runs the Baizhang/Huichang shape without adding a new taxonomy
row or a state-sized being.

Reading and motivation: Identification/Commentary.lean, C.7.
-/

import WeldAndArrow.Consequences.Taxonomy

namespace WAA

namespace Grid

variable {Contrib : Type} [PreorderBot Contrib]
variable (G : Grid Contrib)

namespace DirectedConvention

open BeingConvention

/- ==============================================================================
   Function-side modality
============================================================================== -/

/-- A being mounts responses only at calls in a supplied modality. This is
    neutral function-side vocabulary: the modality is a predicate on calls, not
    a value judgement about the receiver. -/
def MountsOnlyIn (b : G.Being) (M : G.Call -> Prop) : Prop :=
  ∀ c r, G.respondsTo b c = some r -> M c

/-- An actual weld at a modality-restricted receiver carries a call in that
    modality. -/
theorem modality_of_actual
    {M : G.Call -> Prop} {w : G.Weld}
    (hM : MountsOnlyIn G w.agent M) (hactual : G.Actual w) :
    M w.call :=
  hM w.call w.response hactual

/-- Any landing at a modality-restricted receiver carries a call in that
    modality. -/
theorem landing_call_in_modality
    {M : G.Call -> Prop} {deed reception : G.Weld}
    (hM : MountsOnlyIn G reception.agent M)
    (hland : LandsAt G deed reception) :
    M reception.call :=
  modality_of_actual G hM hland.right

/-- A weld whose call lies outside the receiver's modality cannot be actual. -/
theorem not_actual_outside_modality
    {M : G.Call -> Prop} {w : G.Weld}
    (hM : MountsOnlyIn G w.agent M) (hout : ¬ M w.call) :
    ¬ G.Actual w :=
  fun hactual => hout (modality_of_actual G hM hactual)

/-- A reception whose call lies outside the receiver's modality cannot be a
    landing. -/
theorem no_landing_outside_modality
    {M : G.Call -> Prop} {deed reception : G.Weld}
    (hM : MountsOnlyIn G reception.agent M) (hout : ¬ M reception.call) :
    ¬ LandsAt G deed reception :=
  fun hland => hout (landing_call_in_modality G hM hland)

namespace BeingConvention

/-- If every fine tag under a macro tag shares a modality restriction, then any
    landing in that fiber carries a call in the same modality. -/
theorem fiber_landing_call_in_modality
    {Macro : Type} (κ : BeingCoarsening G Macro)
    {b : Macro} {M : G.Call -> Prop}
    (hfiberM : ∀ p : G.Being, κ.proj p = b -> MountsOnlyIn G p M)
    {deed reception : G.Weld}
    (hfiber : κ.InFiber b reception)
    (hland : LandsAt G deed reception) :
    M reception.call :=
  landing_call_in_modality G (hfiberM reception.agent hfiber) hland

end BeingConvention

end DirectedConvention

/- ==============================================================================
   Reception-command language
============================================================================== -/

/-- Claim object for a command that treats reception itself as commanded: this
    deed is asserted to land at that reception. -/
structure ReceptionCommand where
  deed      : G.Weld
  reception : G.Weld

/-- A tiny object language for reception-command claims. Such claims are
    satisfiable only where the field-side delivery reaches an actual reception. -/
def receptionCommandLanguage : ClaimLanguage G where
  Claim := ReceptionCommand G
  Holds
    | .floor, _ => False
    | .actTime _, claim =>
        DirectedConvention.LandsAt G claim.deed claim.reception

/-- A recorded reception-command utterance fits its offered tier only when the
    commanded reception actually lands. -/
theorem receptionCommand_unfit_of_no_landing
    (u : RecordedUtterance G (receptionCommandLanguage G))
    (hnot : ¬ DirectedConvention.LandsAt G u.content.deed u.content.reception) :
    ¬ u.FitsOfferedTier := by
  intro hfit
  change (receptionCommandLanguage G).TrueAt u.offeredAt u.content at hfit
  cases hoff : u.offeredAt with
  | floor =>
      rw [hoff] at hfit
      exact hfit.elim
  | actTime _ =>
      rw [hoff] at hfit
      dsimp [receptionCommandLanguage, ClaimLanguage.TrueAt] at hfit
      exact hnot hfit

namespace DirectedConvention
namespace BeingConvention
namespace GridConvention

/-- The ledger census face delegates to the existing per-call/global row. -/
theorem ledger_census_misfits_live_offer
    (u : RecordedUtterance G (rowLanguage G))
    (hcontent : u.content = .denied .perCallGlobal)
    (hlive : Tier.hasLiveShare G u.offeredAt) :
    ¬ u.FitsOfferedTier :=
  denied_misfits_live_offer G .perCallGlobal u hcontent hlive

/-- The ledger prognosis face delegates to the existing standing/dated row. -/
theorem ledger_prognosis_misfits_live_offer
    (u : RecordedUtterance G (rowLanguage G))
    (hcontent : u.content = .denied .standingDated)
    (hlive : Tier.hasLiveShare G u.offeredAt) :
    ¬ u.FitsOfferedTier :=
  denied_misfits_live_offer G .standingDated u hcontent hlive

end GridConvention
end BeingConvention
end DirectedConvention

end Grid

/- ==============================================================================
   Ledger case
============================================================================== -/

namespace LedgerCase

open Grid
open Grid.DirectedConvention
open Grid.DirectedConvention.BeingConvention

inductive Being
  | master
  | official
  | practitioner
deriving DecidableEq

inductive Call
  | economic
  | floor
  | decree
deriving DecidableEq

inductive Response
  | code
  | comply
  | display
deriving DecidableEq

/-- The economic modality: the one call class the official ledger can receive. -/
def economicModality : Call -> Prop
  | .economic => True
  | .floor    => False
  | .decree   => False

/-- Three beings, three calls, three responses, constant live grade. Delivery
    reaches exactly receptions whose response is `code` or `comply`; actuality
    remains controlled by `respondsTo`. -/
def ledgerGrid : Grid Nat where
  Being      := Being
  Call       := Call
  Response   := Response
  respondsTo b c :=
    match b, c with
    | .master, .economic       => some .code
    | .master, .decree         => some .display
    | .official, .economic     => some .comply
    | .practitioner, .economic => some .code
    | _, _                     => none
  grade _ _ _ := 1
  conditions _ reception :=
    match reception.response with
    | .code    => True
    | .comply  => True
    | .display => False

def codeWeld : ledgerGrid.Weld :=
  ⟨Being.master, Call.economic, Response.code⟩

def officialComplyWeld : ledgerGrid.Weld :=
  ⟨Being.official, Call.economic, Response.comply⟩

def practitionerCodeWeld : ledgerGrid.Weld :=
  ⟨Being.practitioner, Call.economic, Response.code⟩

def decreeWeld : ledgerGrid.Weld :=
  ⟨Being.master, Call.decree, Response.display⟩

def commandedReception : ledgerGrid.Weld :=
  ⟨Being.official, Call.floor, Response.comply⟩

theorem codeWeld_actual :
    ledgerGrid.Actual codeWeld :=
  rfl

theorem officialComplyWeld_actual :
    ledgerGrid.Actual officialComplyWeld :=
  rfl

theorem practitionerCodeWeld_actual :
    ledgerGrid.Actual practitionerCodeWeld :=
  rfl

theorem decreeWeld_actual :
    ledgerGrid.Actual decreeWeld :=
  rfl

theorem official_mountsOnlyIn_economic :
    MountsOnlyIn ledgerGrid Being.official economicModality := by
  intro c r h
  cases c <;> cases r <;>
    simp [ledgerGrid, economicModality] at h ⊢

theorem official_actualAgentInhabited :
    ledgerGrid.ActualAgentInhabited Being.official :=
  ⟨officialComplyWeld, officialComplyWeld_actual, rfl⟩

theorem official_landing_only_economic
    {deed reception : ledgerGrid.Weld}
    (hagent : reception.agent = Being.official)
    (hland : LandsAt ledgerGrid deed reception) :
    economicModality reception.call := by
  cases reception with
  | mk agent call response =>
      cases hagent
      exact landing_call_in_modality ledgerGrid
        official_mountsOnlyIn_economic hland

theorem floor_speech_never_lands_at_official
    {deed reception : ledgerGrid.Weld}
    (hagent : reception.agent = Being.official)
    (hcall : reception.call = Call.floor) :
    ¬ LandsAt ledgerGrid deed reception := by
  intro hland
  have hmod : economicModality reception.call :=
    official_landing_only_economic hagent hland
  rw [hcall] at hmod
  exact hmod

theorem code_lands_at_official :
    LandsAt ledgerGrid codeWeld officialComplyWeld :=
  ⟨True.intro, officialComplyWeld_actual⟩

theorem code_lands_at_practitioner :
    LandsAt ledgerGrid codeWeld practitionerCodeWeld :=
  ⟨True.intro, practitionerCodeWeld_actual⟩

theorem code_ruler_not_exempt :
    LandsAt ledgerGrid codeWeld codeWeld :=
  ⟨True.intro, codeWeld_actual⟩

theorem one_act_two_receivers :
    LandsAt ledgerGrid codeWeld officialComplyWeld ∧
      LandsAt ledgerGrid codeWeld practitionerCodeWeld :=
  ⟨code_lands_at_official, code_lands_at_practitioner⟩

inductive Sector
  | state
  | sangha
deriving DecidableEq

def sectorCoarsening : BeingCoarsening ledgerGrid Sector where
  proj
    | Being.official => Sector.state
    | _              => Sector.sangha

def ledgerSentienceReading : ledgerGrid.SentienceReading :=
  Grid.SentienceReading.allSentient ledgerGrid

theorem state_tag_sentient :
    sectorCoarsening.SentientTag ledgerSentienceReading Sector.state :=
  ⟨officialComplyWeld, ⟨officialComplyWeld_actual, by
      change True
      exact True.intro⟩, rfl⟩

theorem state_fiber_shares_register :
    ∀ p : ledgerGrid.Being,
      sectorCoarsening.proj p = Sector.state ->
        MountsOnlyIn ledgerGrid p economicModality := by
  intro p hp
  cases p with
  | official =>
      exact official_mountsOnlyIn_economic
  | master =>
      cases hp
  | practitioner =>
      cases hp

theorem state_fiber_landing_economic
    {deed reception : ledgerGrid.Weld}
    (hfiber : sectorCoarsening.InFiber Sector.state reception)
    (hland : LandsAt ledgerGrid deed reception) :
    economicModality reception.call :=
  fiber_landing_call_in_modality ledgerGrid sectorCoarsening
    state_fiber_shares_register hfiber hland

theorem commandedReception_delivered :
    DeliveredTo ledgerGrid decreeWeld commandedReception :=
  True.intro

theorem commandedReception_not_actual :
    ¬ ledgerGrid.Actual commandedReception := by
  intro h
  cases h

theorem commandedReception_not_lands :
    ¬ LandsAt ledgerGrid decreeWeld commandedReception :=
  fun hland => commandedReception_not_actual hland.right

def decreeUtterance :
    RecordedUtterance ledgerGrid (receptionCommandLanguage ledgerGrid) where
  weld      := decreeWeld
  actual    := decreeWeld_actual
  offeredAt := Tier.actTime decreeWeld
  content   := { deed := decreeWeld, reception := commandedReception }

theorem decree_utterance_not_fits :
    ¬ decreeUtterance.FitsOfferedTier :=
  receptionCommand_unfit_of_no_landing ledgerGrid
    decreeUtterance commandedReception_not_lands

/-- The decree can engineer the delivery line while failing to command the
    purported reception. -/
theorem decree_engineers_calls_not_receptions :
    DeliveredTo ledgerGrid decreeWeld commandedReception ∧
      ¬ ledgerGrid.Actual commandedReception ∧
        ¬ decreeUtterance.FitsOfferedTier :=
  ⟨commandedReception_delivered, commandedReception_not_actual,
    decree_utterance_not_fits⟩

end LedgerCase

end WAA
