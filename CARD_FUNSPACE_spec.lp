require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4555253 [_107639 _107642] (d : El _107639) : Prf (∀ (λ s : El (fun _107642 bool), (∀ (λ t : El (fun _107639 bool), (⇒ (∧ ((@FINITE _107642) s) ((@FINITE _107639) t)) (= ((@CARD (fun _107642 _107639)) ((@GSPEC (fun _107642 _107639)) (λ GEN_PVAR_149 : El (fun _107642 _107639), (∃ (λ f : El (fun _107642 _107639), ((@SETSPEC (fun _107642 _107639)) GEN_PVAR_149 (∧ (∀ (λ x : El _107642, (⇒ ((@IN _107642) x s) ((@IN _107639) (f x) t)))) (∀ (λ x : El _107642, (⇒ (¬ ((@IN _107642) x s)) (= (f x) d))))) f)))))) (EXP ((@CARD _107639) t) ((@CARD _107642) s))))))));
