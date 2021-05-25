-- Prova de correção de SCiALC, composta por provas de correção de
-- cada regra de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

namespace soundnessSCiALC

open iALCbasics

-- TODO definição de sequente válido

-- TODO abox???????
constants A B : Formula
constant X : Nominal

#check valid_seq (subj_r_n (Proof (Sequent ((Formula.elemOf X A) :: Δ) B)))

-- TODO completar

end soundnessSCiALC