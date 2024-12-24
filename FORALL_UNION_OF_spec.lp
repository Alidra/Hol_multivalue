require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4848609 [_111301] (P : El (fun (fun (fun _111301 bool) bool) bool)) (Q : El (fun (fun _111301 bool) bool)) (R : El (fun (fun _111301 bool) bool)) : Prf (= (∀ (λ s : El (fun _111301 bool), (⇒ ((@UNION_OF _111301) P Q s) (R s)))) (∀ (λ t : El (fun (fun _111301 bool) bool), (⇒ (∧ (P t) (∀ (λ c : El (fun _111301 bool), (⇒ ((@IN (fun _111301 bool)) c t) (Q c))))) (R ((@UNIONS _111301) t))))));
