require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1147887 [_27012] : Prf (∀ (λ P : El (fun _27012 bool), (∀ (λ l1 : El (list _27012), (∀ (λ l2 : El (list _27012), (= ((@FILTER _27012) P ((@APPEND _27012) l1 l2)) ((@APPEND _27012) ((@FILTER _27012) P l1) ((@FILTER _27012) P l2)))))))));
