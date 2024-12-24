require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1148178 [_27039 _27046] : Prf (∀ (λ P : El (fun _27039 bool), (∀ (λ f : El (fun _27046 _27039), (∀ (λ l : El (list _27046), (= ((@FILTER _27039) P ((@MAP _27046 _27039) f l)) ((@MAP _27046 _27039) f ((@FILTER _27046) ((@o _27046 _27039 bool) P f) l)))))))));
