require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4067239 [_102126 _102133] : Prf (∀ (λ P : El (fun (fun _102133 bool) bool), (∀ (λ f : El (fun _102126 _102133), (∀ (λ s : El (fun _102126 bool), (∀ (λ n : El num, (= (∃ (λ t : El (fun _102133 bool), (∧ ((@FINITE _102133) t) (∧ (< ((@CARD _102133) t) n) (∧ ((@SUBSET _102133) t ((@IMAGE _102126 _102133) f s)) (P t)))))) (∃ (λ t : El (fun _102126 bool), (∧ ((@FINITE _102126) t) (∧ (< ((@CARD _102126) t) n) (∧ ((@SUBSET _102126) t s) (∧ (∀ (λ x : El _102126, (∀ (λ y : El _102126, (⇒ (∧ ((@IN _102126) x t) ((@IN _102126) y t)) (= (= (f x) (f y)) (= x y))))))) (P ((@IMAGE _102126 _102133) f t)))))))))))))))));
