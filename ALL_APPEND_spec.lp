require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1160417 [_27241] : Prf (∀ (λ P : El (fun _27241 bool), (∀ (λ l1 : El (list _27241), (∀ (λ l2 : El (list _27241), (= ((@ALL _27241) P ((@APPEND _27241) l1 l2)) (∧ ((@ALL _27241) P l1) ((@ALL _27241) P l2)))))))));
