import Leanspi

namespace Pi

def example_process := pi (Process String String (Ty Security)) {
  new priv : 𝐶' Security.HH ⟦ 𝐶' Security.HH ⟦ Ty.HH ⟧ ⟧;
  !(in(priv, ch : 𝐶' Security.HH ⟦ Ty.HH ⟧);
    new x : Ty.HH;
    out(ch, x))
}

end Pi

def main : IO Unit := do
  let res := Pi.Process.typeCheck Pi.example_process ∅ (wf := Pi.WF.Empty)
  IO.println s!"Result: {res}"
