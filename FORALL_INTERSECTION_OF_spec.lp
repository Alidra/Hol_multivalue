require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4851595 [_111337] (P : El (fun (fun (fun _111337 bool) bool) bool)) (Q : El (fun (fun _111337 bool) bool)) (R : El (fun (fun _111337 bool) bool)) : Prf (= (∀ (λ s : El (fun _111337 bool), (⇒ ((@INTERSECTION_OF _111337) P Q s) (R s)))) (∀ (λ t : El (fun (fun _111337 bool) bool), (⇒ (∧ (P t) (∀ (λ c : El (fun _111337 bool), (⇒ ((@IN (fun _111337 bool)) c t) (Q c))))) (R ((@INTERS _111337) t))))));
