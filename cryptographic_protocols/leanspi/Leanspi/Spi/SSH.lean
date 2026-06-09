import Leanspi.Spi.Process
import Leanspi.Common.TypingEnvironment
import Leanspi.Spi.SecrecyIntegrity

set_option maxHeartbeats 300000

namespace Spi

-- abbreviations for Proess and terms where names and variables are Strings
abbrev SProcess := Process String String (Ty Security)
abbrev STerm := Notation.Pi.Term (SProcess)
-- Ty.LL is a Type, Security.LL is a Level
abbrev Ty.LL : Ty Security := Security.LL
abbrev Ty.LH : Ty Security := Security.LH
abbrev Ty.HL : Ty Security := Security.HL
abbrev Ty.HH : Ty Security := Security.HH
-- Instantiate Term.{Name,Var} to String String
abbrev name := @Term.Name String String
abbrev var := @Term.Var String String
-- Make the Sig/Ver/Dec/Enc/LL/LH/HH names available w/o prefix
open KeyKind Security

-- Tactic to quickly solve  gloas in the form `⊢ WF (Γ + ...)
macro "wf" : tactic =>
  `(tactic| apply_rules [WF.Env, WF.Empty, Term.isNameOrVar.Name, Term.isNameOrVar.Var] <;>
            simp_all[TypingEnvironment.get_none_mem_not] <;>
            done)
-- Tactic to solve goals `⊢ Term.HasType (Γ + ...) M T`
-- if the context contains `Term.HasType Γ M T`
macro "weakening" : tactic => `(tactic| apply_rules[hasType_weakening])
-- General (slow) automation
macro "auto" : tactic => `(tactic|
  aesop (add safe constructors WF,
             safe Term.isNameOrVar,
             safe Term.HasType.Atom,
             simp TypingEnvironment.get_none_mem_not,
             safe Relation.ReflTransGen.single,
             safe constructors Ty.Subtype',
             simp can_flow, simp can_flow_integrity, simp can_flow_confidentiality) )


-- For the proofs in this file you may need to use Subsumption to change a type to a subtype before, e.g., sending it to a public LL channel.
-- This can be done with the tactic `apply Term.HasType.Subsumption (T := LL)`, which applies subsumption and instantiates the resulting type to LL.


def client (net: STerm) (gab vkC skC : STerm) (SSH_MSG_USERAUTH_SUCCESS : STerm) : SProcess := pi {
  out(net, ⦃ vkC ⦄ˢ gab);
  in(net, m₁: Ty.LL);
  case m₁ of ⦃ nₛ ⦄ˢ gab in
  out(net, ⦃ ⟦ nₛ ⟧ skC ⦄ˢ gab);
  in(net, m₂: Ty.LL);
  case m₂ of ⦃ res ⦄ˢ gab in
  if res = SSH_MSG_USERAUTH_SUCCESS then ∅
}

theorem client_wt (hΓ: WF Γ)
                  (hn: net.HasType Γ (𝐶'LL⟦LL⟧))
                  (hc: skC.HasType Γ (Sig𝐾'HH⟦HH⟧))
                  (hg: gab.HasType Γ (Sym𝐾'HH⟦HH⟧))
                  (hs: SSH_MSG_USERAUTH_SUCCESS.HasType Γ LH)
                  (hs₁: var "m₁" ∉ Γ)
                  (hs₂: var "nₛ" ∉ Γ)
                  (hs₃: var "m₂" ∉ Γ)
                  (hs₄: var "res" ∉ Γ)
                  : (client net gab skC.Vk skC SSH_MSG_USERAUTH_SUCCESS).WellTyped Γ := by
  simp[client]
  apply Process.WellTyped.Out
  · show (Term.HasType ?Γ ?M LL)
    apply Term.HasType.Subsumption (T := LL) (T' := LH)
    · apply Term.HasType.SymEnc --we want to show that ⦃ vkC ⦄ˢ has type LH
      . apply hg --key has the right type
      · apply Term.HasType.Subsumption (T := HH) (T' := Ver𝐾'LH⟦HH⟧) --the message has the right type
        apply Term.HasType.VerKey; apply hc --show that skC has type Ver𝐾'LH⟦HH⟧
        apply Relation.ReflTransGen.trans (a:= Ver𝐾'LH⟦HH⟧) (b := LH) (c:= HH) <;> auto --subtyping by transitvity
    · auto --show that LH is a subtype of LL
  · apply Process.WellTyped.In
    · apply Process.WellTyped.SymDec
      · weakening; wf --needs weakening due to new variable m₁
      · apply Term.HasType.Atom; wf; aesop; --m₁ has type LL
      · apply Process.WellTyped.Out
        · show (Term.HasType ?Γ ?M LL)
          apply Term.HasType.Subsumption (T := LL) (T' := LH)
          · apply Term.HasType.SymEnc -- show that ⦃ ⟦ nₛ ⟧ skC ⦄ˢ has type LH
            · weakening <;> wf -- gab has the right type
            · apply Term.HasType.DigSig --show that ⟦ nₛ ⟧ skC is a valid signature of type LH
              · weakening <;> wf --skC has the right type
              · apply Term.HasType.Atom; wf; aesop; --nonce has the right type
              · auto
          · auto
        · apply Process.WellTyped.In
          · apply Process.WellTyped.SymDec
            · weakening <;> wf --gad has the right type
            · apply Term.HasType.Atom; wf; aesop --m₂ has the right type
            · apply Process.WellTyped.Cond
              · apply Term.HasType.Atom; wf; aesop
              · weakening <;> wf
              · apply Process.WellTyped.Stop; wf
              · apply Process.WellTyped.Stop; wf
          · weakening <;> wf -- net has thre right type
        · weakening <;> wf -- net has the right type


    · apply hn -- net has the right type
  · apply hn -- net has the right type



def server  (net: STerm) (gab authorized_key : STerm) (SSH_MSG_USERAUTH_SUCCESS : STerm) : SProcess := pi {
  in(net, m₁: Ty.LL);
  case m₁ of ⦃ vkC ⦄ˢ gab in
  if vkC = authorized_key then
  new nₛ: Ty.HH;
  out(net, ⦃ nₛ ⦄ˢ gab);
  in(net, m₂: Ty.LL);
  case m₂ of ⦃ sig ⦄ˢ gab in
  case sig of ⟦ nₛ' ⟧ authorized_key in
  if nₛ = nₛ' then
  out(net, ⦃ SSH_MSG_USERAUTH_SUCCESS ⦄ˢ gab)
}

theorem server_wt (hΓ: WF Γ)
                  (hn: net.HasType Γ (𝐶'LL⟦LL⟧))
                  (hg: gab.HasType Γ (Sym𝐾'HH⟦HH⟧))
                  (hk: authorized_key.HasType Γ (Ver𝐾'LH⟦HH⟧))
                  (hs: SSH_MSG_USERAUTH_SUCCESS.HasType Γ LH)
                  (hs₁: var "m₁" ∉ Γ)
                  (hs₂: name "nₛ" ∉ Γ)
                  (hs₃: var "m₂" ∉ Γ)
                  (hs₄: var "sig" ∉ Γ)
                  (hs₅: var "nₛ'" ∉ Γ)
                  (hs₆: var "vkC" ∉ Γ)
                  : (server net gab authorized_key SSH_MSG_USERAUTH_SUCCESS).WellTyped Γ := by
  simp[server]
  apply Process.WellTyped.In
  · apply Process.WellTyped.SymDec
    · weakening; wf; --gab has the right type
    · apply Term.HasType.Atom; wf; aesop; --m₁ has the right type
    · apply Process.WellTyped.Cond
      · apply Term.HasType.Atom; wf; aesop --show that vkC is well typed
      · weakening <;> wf --show that authorized_key is well typed
      · apply Process.WellTyped.Res --new nₛ: Ty.HH
        apply Process.WellTyped.Out
        · show (Term.HasType ?Γ ?M LL)
          apply Term.HasType.Subsumption (T := LL) (T' := LH)
          · apply Term.HasType.SymEnc -- (⦃ nₛ ⦄ˢ gab) has type LH
            · weakening <;> wf --gab has the right type
            · apply Term.HasType.Atom; wf; aesop --nₛ has the right type
          · auto --LH is a subtype of LL
        · apply Process.WellTyped.In
          · apply Process.WellTyped.SymDec
            · weakening <;> wf --gab has the right type
            · apply Term.HasType.Atom; wf; aesop --m₂ is well typed
            · apply Process.WellTyped.SignCheck
              · weakening <;>  wf --authorized_key has the right type
              · apply Term.HasType.Atom; wf; aesop --sig has the right type
              · apply Process.WellTyped.Cond
                · apply Term.HasType.Atom; wf; aesop -- nₛ is well typed
                · apply Term.HasType.Atom; wf; aesop -- nₛ' is well typed
                · apply Process.WellTyped.Out
                  · show (Term.HasType ?Γ ?M LL)
                    apply Term.HasType.Subsumption (T := LL) (T' := LH)
                    · apply Term.HasType.SymEnc -- (⦃ SSH_MSG_USERAUTH_SUCCESS ⦄ˢ gab) has type LH
                      · weakening <;> wf --gab has the right type
                      · apply Term.HasType.Subsumption (T := HH) (T' := LH) --subsumption for SSH_MSG_USERAUTH_SUCCESS
                        · weakening <;> wf
                        · auto
                    · auto --LH is a subtype of LL
                  · apply Process.WellTyped.Stop; wf
                  · weakening <;> wf --net has the right type
                · apply Process.WellTyped.Stop; wf
              · auto
          · weakening <;> wf --net has the right type
        · weakening <;> wf --net has the right type
      · apply Process.WellTyped.Stop; wf;
  · apply hn


def ssh : SProcess := pi {
 new net: Ty.LL;
 new gab: (Sym𝐾'HH⟦HH⟧);
 new skC: (Sig𝐾'HH⟦HH⟧);
 new SSH_MSG_USERAUTH_SUCCESS: Ty.LH;
 (! [client net gab (.Vk skC) skC SSH_MSG_USERAUTH_SUCCESS ]) |
 (! [server net gab (.Vk skC) SSH_MSG_USERAUTH_SUCCESS ])
}

-- This theorem proves that the composition of the above processes is well typed if the keys have the correct type.
-- We use an empty environment and we create the keys as restrictions in the process.
theorem ssh_wt : ssh.WellTyped ∅ := by
  simp[ssh]
  apply_rules [Process.WellTyped.Res]
  generalize hΓ:
    ((∅ : TyEnv String String) ++ (name "net", Ty.LL) ++ (name "gab", Sym𝐾'HH⟦HH⟧) ++
    (name "skC", Sig𝐾'HH⟦HH⟧) ++ (name "SSH_MSG_USERAUTH_SUCCESS", Ty.LH)) = Γ
  have wfΓ : WF Γ := by auto
  have hnet : (name "net").HasType Γ (𝐶'LL⟦LL⟧) := by apply Term.HasType.Subsumption <;> auto
  have hg: (name "gab").HasType Γ (Sym𝐾'HH⟦HH⟧) := by auto
  have hv: (Term.Vk (name "skC")).HasType Γ (Ver𝐾'LH⟦HH⟧) := by apply Term.HasType.VerKey; auto
  apply Process.WellTyped.Par <;> apply Process.WellTyped.Repl
  · apply client_wt <;> auto
  · apply server_wt <;> auto
