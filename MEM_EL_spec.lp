require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1160771 [_27264] : Prf (∀ (λ l : El (list _27264), (∀ (λ n : El num, (⇒ (< n ((@LENGTH _27264) l)) ((@MEM _27264) ((@EL _27264) n l) l))))));
