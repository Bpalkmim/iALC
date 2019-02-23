-- Prova de completude de SCiALC, composta por derivações dos axiomas do
-- cálculo de Hilbert para iALC utilizando as regras de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

namespace completenessSCiALC

open axiomsSCiALC
open leftRulesSCiALC
open rightRulesSCiALC

-- Constantes
constants x y : Nominal
constant r : Role

-- Variáveis úteis


variable seq_init : Proof (Sequent (ElemOf y ⊥ :: (Relation r x y :: nil {})) (ElemOf x ⊥))
variable seq_concl : Proof (Sequent (nil {}) (ElemOf x ((Exis r ⊥) ⊑ ⊥)))

TODO opens extras

TODO completar

-- Axioma 4: ∃R.⊥ ⊑ ⊥
check subj_r_n (exists_l (axiom_efq seq_init))
checck seq_concl

TODO completar

end completenessSCiALC