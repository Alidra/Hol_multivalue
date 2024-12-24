require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4582115 [_107705 _107708] (d : El _107705) : Prf (∀ (λ s : El (fun _107708 bool), (∀ (λ t : El (fun _107705 bool), (⇒ (∧ ((@FINITE _107708) s) ((@FINITE _107705) t)) ((@FINITE (fun _107708 _107705)) ((@GSPEC (fun _107708 _107705)) (λ GEN_PVAR_150 : El (fun _107708 _107705), (∃ (λ f : El (fun _107708 _107705), ((@SETSPEC (fun _107708 _107705)) GEN_PVAR_150 (∧ (∀ (λ x : El _107708, (⇒ ((@IN _107708) x s) ((@IN _107705) (f x) t)))) (∀ (λ x : El _107708, (⇒ (¬ ((@IN _107708) x s)) (= (f x) d))))) f)))))))))));
