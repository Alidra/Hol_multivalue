Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_PCROSS_EQ_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_EMPTY_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_PCROSS_spec.
Require Import FINITE_SUBSET_spec.
Require Import FSTCART_PASTECART_spec.
Require Import IN_IMAGE_spec.
Require Import PASTECART_IN_PCROSS_spec.
Require Import PCROSS_EMPTY_spec.
Require Import SNDCART_PASTECART_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm7662554_spec.
Require Import thm7664352_spec.
Require Import thm82_spec.
Lemma lem8030150 {A M N : Type'} (x : cart A M) : term0 A M N x.
Proof. exact (@lem7648197 A M N x). Qed.
Lemma lem8030151 {A M N : Type'} (x : cart A M) : (term0 A M N x) = (term1 A M N x).
Proof. exact (eq_refl (term0 A M N x)). Qed.
Lemma lem8030152 {A M N : Type'} (x : cart A M) : term1 A M N x.
Proof. exact (EQ_MP (@lem8030151 A M N x) (@lem8030150 A M N x)). Qed.
Lemma lem8030153 {A M N : Type'} (x : cart A M) (y : cart A N) : term2 A M N x y.
Proof. exact (@lem8030152 A M N x y). Qed.
Lemma lem8030154 {A M N : Type'} (x : cart A M) (y : cart A N) : (term2 A M N x y) = ((term3 A M N x y) = y).
Proof. exact (eq_refl (term2 A M N x y)). Qed.
Lemma lem8030156 {A M N : Type'} (x : cart A M) : term4 A M N x.
Proof. exact (@lem7643282 A M N x). Qed.
Lemma lem8030157 {A M N : Type'} (x : cart A M) : (term4 A M N x) = (term5 A M N x).
Proof. exact (eq_refl (term4 A M N x)). Qed.
Lemma lem8030158 {A M N : Type'} (x : cart A M) : term5 A M N x.
Proof. exact (EQ_MP (@lem8030157 A M N x) (@lem8030156 A M N x)). Qed.
Lemma lem8030159 {A M N : Type'} (x : cart A M) (y : cart A N) : term6 A M N x y.
Proof. exact (@lem8030158 A M N x y). Qed.
Lemma lem8030160 {A M N : Type'} (y : cart A N) (x : cart A M) : (term6 A M N x y) = ((term7 A M N x y) = x).
Proof. exact (eq_refl (term6 A M N x y)). Qed.
Lemma lem8030162 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term8 _141927 _141928 _141929 s.
Proof. exact (@lem8004229 _141927 _141928 _141929 s). Qed.
Lemma lem8030163 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term8 _141927 _141928 _141929 s) = (term9 _141927 _141928 _141929 s).
Proof. exact (eq_refl (term8 _141927 _141928 _141929 s)). Qed.
Lemma lem8030164 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term9 _141927 _141928 _141929 s.
Proof. exact (EQ_MP (@lem8030163 _141927 _141928 _141929 s) (@lem8030162 _141927 _141928 _141929 s)). Qed.
Lemma lem8030165 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term10 _141927 _141928 _141929 s t.
Proof. exact (@lem8030164 _141927 _141928 _141929 s t). Qed.
Lemma lem8030166 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term10 _141927 _141928 _141929 s t) = (term11 _141927 _141928 _141929 s t).
Proof. exact (eq_refl (term10 _141927 _141928 _141929 s t)). Qed.
Lemma lem8030167 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term11 _141927 _141928 _141929 s t.
Proof. exact (EQ_MP (@lem8030166 _141927 _141928 _141929 s t) (@lem8030165 _141927 _141928 _141929 s t)). Qed.
Lemma lem8030168 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : term12 _141927 _141928 _141929 s t x.
Proof. exact (@lem8030167 _141927 _141928 _141929 s t x). Qed.
Lemma lem8030169 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term12 _141927 _141928 _141929 s t x) = (term13 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term12 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8030170 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term13 _141927 _141928 _141929 x s t.
Proof. exact (EQ_MP (@lem8030169 _141927 _141928 _141929 x s t) (@lem8030168 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8030171 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : term14 _141927 _141928 _141929 x s t y.
Proof. exact (@lem8030170 _141927 _141928 _141929 x s t y). Qed.
Lemma lem8030172 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term14 _141927 _141928 _141929 x s t y) = ((term15 _141927 _141928 _141929 x y s t) = (term16 _141927 _141928 _141929 x s y t)).
Proof. exact (eq_refl (term14 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8030174 {A : Type'} (h1 : term17 A) : term17 A.
Proof. exact (h1). Qed.
Lemma lem8030175 {A : Type'} (s : A -> Prop) (h1 : term17 A) : term18 A s.
Proof. exact (@lem8030174 A h1 s). Qed.
Lemma lem8030176 {A : Type'} (s : A -> Prop) : (term18 A s) = (term19 A s).
Proof. exact (eq_refl (term18 A s)). Qed.
Lemma lem8030177 {A : Type'} (s : A -> Prop) (h1 : term17 A) : term19 A s.
Proof. exact (EQ_MP (@lem8030176 A s) (@lem8030175 A s h1)). Qed.
Lemma lem8030178 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term17 A) : term20 A s t.
Proof. exact (@lem8030177 A s h1 t). Qed.
Lemma lem8030179 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term20 A s t) = (term21 A t s).
Proof. exact (eq_refl (term20 A s t)). Qed.
Lemma lem8030180 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term17 A) : term21 A t s.
Proof. exact (EQ_MP (@lem8030179 A t s) (@lem8030178 A s t h1)). Qed.
Lemma lem8030181 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term22 A s t) : term22 A s t.
Proof. exact (h1). Qed.
Lemma lem8030182 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term17 A) (h2 : term22 A s t) : @FINITE A s.
Proof. exact (@lem8030180 A t s h1 (@lem8030181 A s t h2)). Qed.
Lemma lem8030183 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term22 A s t) : term23 A s.
Proof. exact (fun h0 : term17 A => @lem8030182 A s t h0 h1). Qed.
Lemma lem8030184 {A : Type'} (s : A -> Prop) (h1 : term24 A s) : term24 A s.
Proof. exact (h1). Qed.
Lemma lem8030185 {A : Type'} (s : A -> Prop) (h1 : term24 A s) : term23 A s.
Proof. exact (ex_elim (@lem8030184 A s h1) (fun t : A -> Prop => fun h0 : term25 A s t => @lem8030183 A s t h0)). Qed.
Lemma lem8030186 {A : Type'} (h1 : term17 A) : term17 A.
Proof. exact (h1). Qed.
Lemma lem8030187 {A : Type'} (s : A -> Prop) (h1 : term17 A) (h2 : term24 A s) : @FINITE A s.
Proof. exact (@lem8030185 A s h2 (@lem8030186 A h1)). Qed.
Lemma lem8030188 {A : Type'} (s : A -> Prop) (h1 : term17 A) : term26 A s.
Proof. exact (fun h0 : term24 A s => @lem8030187 A s h1 h0). Qed.
Lemma lem8030189 {A : Type'} (h1 : term17 A) : term27 A.
Proof. exact (fun s : A -> Prop => @lem8030188 A s h1). Qed.
Lemma lem8030190 {A : Type'} : term28 A.
Proof. exact (fun h0 : term17 A => @lem8030189 A h0). Qed.
Lemma lem8030191 {A : Type'} : term27 A.
Proof. exact (@lem8030190 A (@lem3599924 A)). Qed.
Lemma lem8030192 {A : Type'} (s : A -> Prop) : term29 A s.
Proof. exact (@lem8030191 A s). Qed.
Lemma lem8030193 {A : Type'} (s : A -> Prop) : (term29 A s) = (term26 A s).
Proof. exact (eq_refl (term29 A s)). Qed.
Lemma lem8030195 {A M N : Type'} (s : type24 A M) : term30 A M N s.
Proof. exact (@lem8030149 A M N s). Qed.
Lemma lem8030196 {A M N : Type'} (s : type24 A M) : (term30 A M N s) = (term31 A M N s).
Proof. exact (eq_refl (term30 A M N s)). Qed.
Lemma lem8030197 {A M N : Type'} (s : type24 A M) : term31 A M N s.
Proof. exact (EQ_MP (@lem8030196 A M N s) (@lem8030195 A M N s)). Qed.
Lemma lem8030198 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term32 A M N s t.
Proof. exact (@lem8030197 A M N s t). Qed.
Lemma lem8030199 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term32 A M N s t) = (term33 A M N s t).
Proof. exact (eq_refl (term32 A M N s t)). Qed.
Lemma lem8030200 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term33 A M N s t.
Proof. exact (EQ_MP (@lem8030199 A M N s t) (@lem8030198 A M N s t)). Qed.
Lemma lem8030201 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term34 A M N s t) : term34 A M N s t.
Proof. exact (h1). Qed.
Lemma lem8030202 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term34 A M N s t) : term35 A M N s t.
Proof. exact (@lem8030200 A M N s t (@lem8030201 A M N s t h1)). Qed.
Lemma lem8030203 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term35 A M N s t) = ((term35 A M N s t) = True).
Proof. exact (@lem7 (term35 A M N s t)). Qed.
Lemma lem8030204 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term34 A M N s t) : (term35 A M N s t) = True.
Proof. exact (EQ_MP (@lem8030203 A M N s t) (@lem8030202 A M N s t h1)). Qed.
Lemma lem8030210 {A M : Type'} (s : type24 A M) : term36 A M s.
Proof. exact (@lem9784 (s = (@EMPTY (cart A M)))). Qed.
Lemma lem8030211 {A M : Type'} (s : type24 A M) : (term36 A M s) = (term37 A M s).
Proof. exact (eq_refl (term36 A M s)). Qed.
Lemma lem8030212 {A M : Type'} (s : type24 A M) : term37 A M s.
Proof. exact (EQ_MP (@lem8030211 A M s) (@lem8030210 A M s)). Qed.
Lemma lem8030214 {A M : Type'} (s : type24 A M) (h1 : term38 A M s) : term38 A M s.
Proof. exact (h1). Qed.
Lemma lem8030215 {A N : Type'} (t : type24 A N) : term36 A N t.
Proof. exact (@lem9784 (t = (@EMPTY (cart A N)))). Qed.
Lemma lem8030216 {A N : Type'} (t : type24 A N) : (term36 A N t) = (term37 A N t).
Proof. exact (eq_refl (term36 A N t)). Qed.
Lemma lem8030217 {A N : Type'} (t : type24 A N) : term37 A N t.
Proof. exact (EQ_MP (@lem8030216 A N t) (@lem8030215 A N t)). Qed.
Lemma lem8030219 {A N : Type'} (t : type24 A N) (h1 : term38 A N t) : term38 A N t.
Proof. exact (h1). Qed.
Lemma lem8030220 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem8030222 {_141994 _141995 _141996 : Type'} : term39 _141994 _141995 _141996.
Proof. exact (proj2 (@lem8005965 Prop Prop Prop _141994 _141995 _141996)). Qed.
Lemma lem8030223 {_141994 _141995 _141996 : Type'} (t : type24 _141994 _141996) : term40 _141994 _141995 _141996 t.
Proof. exact (@lem8030222 _141994 _141995 _141996 t). Qed.
Lemma lem8030224 {_141994 _141995 _141996 : Type'} (t : type24 _141994 _141996) : (term40 _141994 _141995 _141996 t) = ((@PCROSS _141994 _141995 _141996 (@EMPTY (cart _141994 _141995)) t) = (@EMPTY (cart _141994 (finite_sum _141995 _141996)))).
Proof. exact (eq_refl (term40 _141994 _141995 _141996 t)). Qed.
Lemma lem8030233 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : s = (@EMPTY (cart A M)).
Proof. exact (h1). Qed.
Lemma lem8030234 {A M N : Type'} : (@PCROSS A M N) = (@PCROSS A M N).
Proof. exact (eq_refl (@PCROSS A M N)). Qed.
Lemma lem8030235 {A M N : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (@PCROSS A M N s) = (@PCROSS A M N (@EMPTY (cart A M))).
Proof. exact (MK_COMB (@lem8030234 A M N) (@lem8030233 A M s h1)). Qed.
Lemma lem8030237 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : t = (@EMPTY (cart A N)).
Proof. exact (h1). Qed.
Lemma lem8030238 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : s = (@EMPTY (cart A M))) (h2 : t = (@EMPTY (cart A N))) : (@PCROSS A M N s t) = (@PCROSS A M N (@EMPTY (cart A M)) (@EMPTY (cart A N))).
Proof. exact (MK_COMB (@lem8030235 A M N s h1) (@lem8030237 A N t h2)). Qed.
Lemma lem8030240 {_141994 _141995 _141996 : Type'} (t : type24 _141994 _141996) : (@PCROSS _141994 _141995 _141996 (@EMPTY (cart _141994 _141995)) t) = (@EMPTY (cart _141994 (finite_sum _141995 _141996))).
Proof. exact (EQ_MP (@lem8030224 _141994 _141995 _141996 t) (@lem8030223 _141994 _141995 _141996 t)). Qed.
Lemma lem8030241 {A M N : Type'} (t : type24 A N) : (@PCROSS A M N (@EMPTY (cart A M)) t) = (@EMPTY (cart A (finite_sum M N))).
Proof. exact (@lem8030240 A M N t). Qed.
Lemma lem8030242 {A M N : Type'} : (@PCROSS A M N (@EMPTY (cart A M)) (@EMPTY (cart A N))) = (@EMPTY (cart A (finite_sum M N))).
Proof. exact (@lem8030241 A M N (@EMPTY (cart A N))). Qed.
Lemma lem8030243 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : s = (@EMPTY (cart A M))) (h2 : t = (@EMPTY (cart A N))) : (@PCROSS A M N s t) = (@EMPTY (cart A (finite_sum M N))).
Proof. exact (TRANS (@lem8030238 A M N s t h1 h2) (@lem8030242 A M N)). Qed.
Lemma lem8030244 {A M N : Type'} : (@FINITE (cart A (finite_sum M N))) = (@FINITE (cart A (finite_sum M N))).
Proof. exact (eq_refl (@FINITE (cart A (finite_sum M N)))). Qed.
Lemma lem8030245 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : s = (@EMPTY (cart A M))) (h2 : t = (@EMPTY (cart A N))) : (term35 A M N s t) = (@FINITE (cart A (finite_sum M N)) (@EMPTY (cart A (finite_sum M N)))).
Proof. exact (MK_COMB (@lem8030244 A M N) (@lem8030243 A M N s t h1 h2)). Qed.
Lemma lem8030247 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem8030220 _92140) (@lem3596285 _92140)). Qed.
Lemma lem8030248 {A M N : Type'} : (@FINITE (cart A (finite_sum M N)) (@EMPTY (cart A (finite_sum M N)))) = True.
Proof. exact (@lem8030247 (type2 A M N)). Qed.
Lemma lem8030249 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : s = (@EMPTY (cart A M))) (h2 : t = (@EMPTY (cart A N))) : (term35 A M N s t) = True.
Proof. exact (TRANS (@lem8030245 A M N s t h1 h2) (@lem8030248 A M N)). Qed.
Lemma lem8030250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8030251 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : s = (@EMPTY (cart A M))) (h2 : t = (@EMPTY (cart A N))) : (term41 A M N s t) = (@eq Prop True).
Proof. exact (MK_COMB (@lem8030250) (@lem8030249 A M N s t h1 h2)). Qed.
Lemma lem8030257 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : s = (@EMPTY (cart A M)).
Proof. exact (h1). Qed.
Lemma lem8030258 {A M : Type'} : (@eq ((cart A M) -> Prop)) = (@eq ((cart A M) -> Prop)).
Proof. exact (eq_refl (@eq ((cart A M) -> Prop))). Qed.
Lemma lem8030259 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (@eq ((cart A M) -> Prop) s) = (@eq ((cart A M) -> Prop) (@EMPTY (cart A M))).
Proof. exact (MK_COMB (@lem8030258 A M) (@lem8030257 A M s h1)). Qed.
Lemma lem8030260 {A M : Type'} : (@EMPTY (cart A M)) = (@EMPTY (cart A M)).
Proof. exact (eq_refl (@EMPTY (cart A M))). Qed.
Lemma lem8030261 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (s = (@EMPTY (cart A M))) = ((@EMPTY (cart A M)) = (@EMPTY (cart A M))).
Proof. exact (MK_COMB (@lem8030259 A M s h1) (@lem8030260 A M)). Qed.
Lemma lem8030263 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8030264 {A M : Type'} (x : type24 A M) : (x = x) = True.
Proof. exact (@lem8030263 (type24 A M) x). Qed.
Lemma lem8030265 {A M : Type'} : ((@EMPTY (cart A M)) = (@EMPTY (cart A M))) = True.
Proof. exact (@lem8030264 A M (@EMPTY (cart A M))). Qed.
Lemma lem8030266 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (s = (@EMPTY (cart A M))) = True.
Proof. exact (TRANS (@lem8030261 A M s h1) (@lem8030265 A M)). Qed.
Lemma lem8030267 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8030268 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (term42 A M s) = (or True).
Proof. exact (MK_COMB (@lem8030267) (@lem8030266 A M s h1)). Qed.
Lemma lem8030274 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : t = (@EMPTY (cart A N)).
Proof. exact (h1). Qed.
Lemma lem8030275 {A N : Type'} : (@eq ((cart A N) -> Prop)) = (@eq ((cart A N) -> Prop)).
Proof. exact (eq_refl (@eq ((cart A N) -> Prop))). Qed.
Lemma lem8030276 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (@eq ((cart A N) -> Prop) t) = (@eq ((cart A N) -> Prop) (@EMPTY (cart A N))).
Proof. exact (MK_COMB (@lem8030275 A N) (@lem8030274 A N t h1)). Qed.
Lemma lem8030277 {A N : Type'} : (@EMPTY (cart A N)) = (@EMPTY (cart A N)).
Proof. exact (eq_refl (@EMPTY (cart A N))). Qed.
Lemma lem8030278 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (t = (@EMPTY (cart A N))) = ((@EMPTY (cart A N)) = (@EMPTY (cart A N))).
Proof. exact (MK_COMB (@lem8030276 A N t h1) (@lem8030277 A N)). Qed.
Lemma lem8030280 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8030281 {A N : Type'} (x : type24 A N) : (x = x) = True.
Proof. exact (@lem8030280 (type24 A N) x). Qed.
Lemma lem8030282 {A N : Type'} : ((@EMPTY (cart A N)) = (@EMPTY (cart A N))) = True.
Proof. exact (@lem8030281 A N (@EMPTY (cart A N))). Qed.
Lemma lem8030283 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (t = (@EMPTY (cart A N))) = True.
Proof. exact (TRANS (@lem8030278 A N t h1) (@lem8030282 A N)). Qed.
Lemma lem8030284 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8030285 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (term42 A N t) = (or True).
Proof. exact (MK_COMB (@lem8030284) (@lem8030283 A N t h1)). Qed.
Lemma lem8030289 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : s = (@EMPTY (cart A M)).
Proof. exact (h1). Qed.
Lemma lem8030290 {A M : Type'} : (@FINITE (cart A M)) = (@FINITE (cart A M)).
Proof. exact (eq_refl (@FINITE (cart A M))). Qed.
Lemma lem8030291 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (@FINITE (cart A M) s) = (@FINITE (cart A M) (@EMPTY (cart A M))).
Proof. exact (MK_COMB (@lem8030290 A M) (@lem8030289 A M s h1)). Qed.
Lemma lem8030293 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem8030220 _92140) (@lem3596285 _92140)). Qed.
Lemma lem8030294 {A M : Type'} : (@FINITE (cart A M) (@EMPTY (cart A M))) = True.
Proof. exact (@lem8030293 (cart A M)). Qed.
Lemma lem8030295 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (@FINITE (cart A M) s) = True.
Proof. exact (TRANS (@lem8030291 A M s h1) (@lem8030294 A M)). Qed.
Lemma lem8030296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8030297 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (term43 A M s) = (and True).
Proof. exact (MK_COMB (@lem8030296) (@lem8030295 A M s h1)). Qed.
Lemma lem8030299 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : t = (@EMPTY (cart A N)).
Proof. exact (h1). Qed.
Lemma lem8030300 {A N : Type'} : (@FINITE (cart A N)) = (@FINITE (cart A N)).
Proof. exact (eq_refl (@FINITE (cart A N))). Qed.
Lemma lem8030301 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (@FINITE (cart A N) t) = (@FINITE (cart A N) (@EMPTY (cart A N))).
Proof. exact (MK_COMB (@lem8030300 A N) (@lem8030299 A N t h1)). Qed.
Lemma lem8030303 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem8030220 _92140) (@lem3596285 _92140)). Qed.
Lemma lem8030304 {A N : Type'} : (@FINITE (cart A N) (@EMPTY (cart A N))) = True.
Proof. exact (@lem8030303 (cart A N)). Qed.
Lemma lem8030305 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (@FINITE (cart A N) t) = True.
Proof. exact (TRANS (@lem8030301 A N t h1) (@lem8030304 A N)). Qed.
Lemma lem8030306 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : s = (@EMPTY (cart A M))) (h2 : t = (@EMPTY (cart A N))) : (term34 A M N s t) = (True /\ True).
Proof. exact (MK_COMB (@lem8030297 A M s h1) (@lem8030305 A N t h2)). Qed.
Lemma lem8030308 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8030309 : (True /\ True) = True.
Proof. exact (@lem8030308 True). Qed.
Lemma lem8030310 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : s = (@EMPTY (cart A M))) (h2 : t = (@EMPTY (cart A N))) : (term34 A M N s t) = True.
Proof. exact (TRANS (@lem8030306 A M N s t h1 h2) (@lem8030309)). Qed.
Lemma lem8030311 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : s = (@EMPTY (cart A M))) (h2 : t = (@EMPTY (cart A N))) : (term44 A M N s t) = (True \/ True).
Proof. exact (MK_COMB (@lem8030285 A N t h2) (@lem8030310 A M N s t h1 h2)). Qed.
Lemma lem8030313 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem8030314 : (True \/ True) = True.
Proof. exact (@lem8030313 True). Qed.
Lemma lem8030315 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : s = (@EMPTY (cart A M))) (h2 : t = (@EMPTY (cart A N))) : (term44 A M N s t) = True.
Proof. exact (TRANS (@lem8030311 A M N s t h1 h2) (@lem8030314)). Qed.
Lemma lem8030316 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : s = (@EMPTY (cart A M))) (h2 : t = (@EMPTY (cart A N))) : (term45 A M N s t) = (True \/ True).
Proof. exact (MK_COMB (@lem8030268 A M s h1) (@lem8030315 A M N s t h1 h2)). Qed.
Lemma lem8030318 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem8030319 : (True \/ True) = True.
Proof. exact (@lem8030318 True). Qed.
Lemma lem8030320 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : s = (@EMPTY (cart A M))) (h2 : t = (@EMPTY (cart A N))) : (term45 A M N s t) = True.
Proof. exact (TRANS (@lem8030316 A M N s t h1 h2) (@lem8030319)). Qed.
Lemma lem8030321 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : s = (@EMPTY (cart A M))) (h2 : t = (@EMPTY (cart A N))) : ((term35 A M N s t) = (term45 A M N s t)) = (True = True).
Proof. exact (MK_COMB (@lem8030251 A M N s t h1 h2) (@lem8030320 A M N s t h1 h2)). Qed.
Lemma lem8030323 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem8030324 : (True = True) = True.
Proof. exact (@lem8030323 True). Qed.
Lemma lem8030325 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : s = (@EMPTY (cart A M))) (h2 : t = (@EMPTY (cart A N))) : ((term35 A M N s t) = (term45 A M N s t)) = True.
Proof. exact (TRANS (@lem8030321 A M N s t h1 h2) (@lem8030324)). Qed.
Lemma lem8030326 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : s = (@EMPTY (cart A M))) (h2 : t = (@EMPTY (cart A N))) : True = ((term35 A M N s t) = (term45 A M N s t)).
Proof. exact (SYM (@lem8030325 A M N s t h1 h2)). Qed.
Lemma lem8030327 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : s = (@EMPTY (cart A M))) (h2 : t = (@EMPTY (cart A N))) : (term35 A M N s t) = (term45 A M N s t).
Proof. exact (EQ_MP (@lem8030326 A M N s t h1 h2) (@lem0)). Qed.
Lemma lem8030328 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem8030330 {_141994 _141995 _141996 : Type'} : term39 _141994 _141995 _141996.
Proof. exact (proj2 (@lem8005965 Prop Prop Prop _141994 _141995 _141996)). Qed.
Lemma lem8030331 {_141994 _141995 _141996 : Type'} (t : type24 _141994 _141996) : term40 _141994 _141995 _141996 t.
Proof. exact (@lem8030330 _141994 _141995 _141996 t). Qed.
Lemma lem8030332 {_141994 _141995 _141996 : Type'} (t : type24 _141994 _141996) : (term40 _141994 _141995 _141996 t) = ((@PCROSS _141994 _141995 _141996 (@EMPTY (cart _141994 _141995)) t) = (@EMPTY (cart _141994 (finite_sum _141995 _141996)))).
Proof. exact (eq_refl (term40 _141994 _141995 _141996 t)). Qed.
Lemma lem8030338 {A N : Type'} (t : type24 A N) : term46 A N t.
Proof. exact (@lem82 (t = (@EMPTY (cart A N)))). Qed.
Lemma lem8030354 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : s = (@EMPTY (cart A M)).
Proof. exact (h1). Qed.
Lemma lem8030355 {A M N : Type'} : (@PCROSS A M N) = (@PCROSS A M N).
Proof. exact (eq_refl (@PCROSS A M N)). Qed.
Lemma lem8030356 {A M N : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (@PCROSS A M N s) = (@PCROSS A M N (@EMPTY (cart A M))).
Proof. exact (MK_COMB (@lem8030355 A M N) (@lem8030354 A M s h1)). Qed.
Lemma lem8030357 {A N : Type'} (t : type24 A N) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem8030358 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (@PCROSS A M N s t) = (@PCROSS A M N (@EMPTY (cart A M)) t).
Proof. exact (MK_COMB (@lem8030356 A M N s h1) (@lem8030357 A N t)). Qed.
Lemma lem8030360 {_141994 _141995 _141996 : Type'} (t : type24 _141994 _141996) : (@PCROSS _141994 _141995 _141996 (@EMPTY (cart _141994 _141995)) t) = (@EMPTY (cart _141994 (finite_sum _141995 _141996))).
Proof. exact (EQ_MP (@lem8030332 _141994 _141995 _141996 t) (@lem8030331 _141994 _141995 _141996 t)). Qed.
Lemma lem8030361 {A M N : Type'} (t : type24 A N) : (@PCROSS A M N (@EMPTY (cart A M)) t) = (@EMPTY (cart A (finite_sum M N))).
Proof. exact (@lem8030360 A M N t). Qed.
Lemma lem8030362 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (@PCROSS A M N s t) = (@EMPTY (cart A (finite_sum M N))).
Proof. exact (TRANS (@lem8030358 A M N t s h1) (@lem8030361 A M N t)). Qed.
Lemma lem8030363 {A M N : Type'} : (@FINITE (cart A (finite_sum M N))) = (@FINITE (cart A (finite_sum M N))).
Proof. exact (eq_refl (@FINITE (cart A (finite_sum M N)))). Qed.
Lemma lem8030364 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (term35 A M N s t) = (@FINITE (cart A (finite_sum M N)) (@EMPTY (cart A (finite_sum M N)))).
Proof. exact (MK_COMB (@lem8030363 A M N) (@lem8030362 A M N t s h1)). Qed.
Lemma lem8030366 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem8030328 _92140) (@lem3596285 _92140)). Qed.
Lemma lem8030367 {A M N : Type'} : (@FINITE (cart A (finite_sum M N)) (@EMPTY (cart A (finite_sum M N)))) = True.
Proof. exact (@lem8030366 (type2 A M N)). Qed.
Lemma lem8030368 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (term35 A M N s t) = True.
Proof. exact (TRANS (@lem8030364 A M N t s h1) (@lem8030367 A M N)). Qed.
Lemma lem8030369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8030370 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (term41 A M N s t) = (@eq Prop True).
Proof. exact (MK_COMB (@lem8030369) (@lem8030368 A M N t s h1)). Qed.
Lemma lem8030376 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : s = (@EMPTY (cart A M)).
Proof. exact (h1). Qed.
Lemma lem8030377 {A M : Type'} : (@eq ((cart A M) -> Prop)) = (@eq ((cart A M) -> Prop)).
Proof. exact (eq_refl (@eq ((cart A M) -> Prop))). Qed.
Lemma lem8030378 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (@eq ((cart A M) -> Prop) s) = (@eq ((cart A M) -> Prop) (@EMPTY (cart A M))).
Proof. exact (MK_COMB (@lem8030377 A M) (@lem8030376 A M s h1)). Qed.
Lemma lem8030379 {A M : Type'} : (@EMPTY (cart A M)) = (@EMPTY (cart A M)).
Proof. exact (eq_refl (@EMPTY (cart A M))). Qed.
Lemma lem8030380 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (s = (@EMPTY (cart A M))) = ((@EMPTY (cart A M)) = (@EMPTY (cart A M))).
Proof. exact (MK_COMB (@lem8030378 A M s h1) (@lem8030379 A M)). Qed.
Lemma lem8030382 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8030383 {A M : Type'} (x : type24 A M) : (x = x) = True.
Proof. exact (@lem8030382 (type24 A M) x). Qed.
Lemma lem8030384 {A M : Type'} : ((@EMPTY (cart A M)) = (@EMPTY (cart A M))) = True.
Proof. exact (@lem8030383 A M (@EMPTY (cart A M))). Qed.
Lemma lem8030385 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (s = (@EMPTY (cart A M))) = True.
Proof. exact (TRANS (@lem8030380 A M s h1) (@lem8030384 A M)). Qed.
Lemma lem8030386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8030387 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (term42 A M s) = (or True).
Proof. exact (MK_COMB (@lem8030386) (@lem8030385 A M s h1)). Qed.
Lemma lem8030391 {A N : Type'} (t : type24 A N) (h1 : term38 A N t) : (t = (@EMPTY (cart A N))) = False.
Proof. exact (@lem8030338 A N t (@lem8030219 A N t h1)). Qed.
Lemma lem8030392 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8030393 {A N : Type'} (t : type24 A N) (h1 : term38 A N t) : (term42 A N t) = (or False).
Proof. exact (MK_COMB (@lem8030392) (@lem8030391 A N t h1)). Qed.
Lemma lem8030397 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : s = (@EMPTY (cart A M)).
Proof. exact (h1). Qed.
Lemma lem8030398 {A M : Type'} : (@FINITE (cart A M)) = (@FINITE (cart A M)).
Proof. exact (eq_refl (@FINITE (cart A M))). Qed.
Lemma lem8030399 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (@FINITE (cart A M) s) = (@FINITE (cart A M) (@EMPTY (cart A M))).
Proof. exact (MK_COMB (@lem8030398 A M) (@lem8030397 A M s h1)). Qed.
Lemma lem8030401 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem8030328 _92140) (@lem3596285 _92140)). Qed.
Lemma lem8030402 {A M : Type'} : (@FINITE (cart A M) (@EMPTY (cart A M))) = True.
Proof. exact (@lem8030401 (cart A M)). Qed.
Lemma lem8030403 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (@FINITE (cart A M) s) = True.
Proof. exact (TRANS (@lem8030399 A M s h1) (@lem8030402 A M)). Qed.
Lemma lem8030404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8030405 {A M : Type'} (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (term43 A M s) = (and True).
Proof. exact (MK_COMB (@lem8030404) (@lem8030403 A M s h1)). Qed.
Lemma lem8030406 {A N : Type'} (t : type24 A N) : (@FINITE (cart A N) t) = (@FINITE (cart A N) t).
Proof. exact (eq_refl (@FINITE (cart A N) t)). Qed.
Lemma lem8030407 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (term34 A M N s t) = (term47 A N t).
Proof. exact (MK_COMB (@lem8030405 A M s h1) (@lem8030406 A N t)). Qed.
Lemma lem8030409 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8030410 {A N : Type'} (t : type24 A N) : (term47 A N t) = (@FINITE (cart A N) t).
Proof. exact (@lem8030409 (@FINITE (cart A N) t)). Qed.
Lemma lem8030411 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (term34 A M N s t) = (@FINITE (cart A N) t).
Proof. exact (TRANS (@lem8030407 A M N t s h1) (@lem8030410 A N t)). Qed.
Lemma lem8030412 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : term38 A N t) (h2 : s = (@EMPTY (cart A M))) : (term44 A M N s t) = (term48 A N t).
Proof. exact (MK_COMB (@lem8030393 A N t h1) (@lem8030411 A M N t s h2)). Qed.
Lemma lem8030414 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem8030415 {A N : Type'} (t : type24 A N) : (term48 A N t) = (@FINITE (cart A N) t).
Proof. exact (@lem8030414 (@FINITE (cart A N) t)). Qed.
Lemma lem8030416 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : term38 A N t) (h2 : s = (@EMPTY (cart A M))) : (term44 A M N s t) = (@FINITE (cart A N) t).
Proof. exact (TRANS (@lem8030412 A M N t s h1 h2) (@lem8030415 A N t)). Qed.
Lemma lem8030417 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : term38 A N t) (h2 : s = (@EMPTY (cart A M))) : (term45 A M N s t) = (term49 A N t).
Proof. exact (MK_COMB (@lem8030387 A M s h2) (@lem8030416 A M N t s h1 h2)). Qed.
Lemma lem8030419 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem8030420 {A N : Type'} (t : type24 A N) : (term49 A N t) = True.
Proof. exact (@lem8030419 (@FINITE (cart A N) t)). Qed.
Lemma lem8030421 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : term38 A N t) (h2 : s = (@EMPTY (cart A M))) : (term45 A M N s t) = True.
Proof. exact (TRANS (@lem8030417 A M N t s h1 h2) (@lem8030420 A N t)). Qed.
Lemma lem8030422 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : term38 A N t) (h2 : s = (@EMPTY (cart A M))) : ((term35 A M N s t) = (term45 A M N s t)) = (True = True).
Proof. exact (MK_COMB (@lem8030370 A M N t s h2) (@lem8030421 A M N t s h1 h2)). Qed.
Lemma lem8030424 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem8030425 : (True = True) = True.
Proof. exact (@lem8030424 True). Qed.
Lemma lem8030426 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : term38 A N t) (h2 : s = (@EMPTY (cart A M))) : ((term35 A M N s t) = (term45 A M N s t)) = True.
Proof. exact (TRANS (@lem8030422 A M N t s h1 h2) (@lem8030425)). Qed.
Lemma lem8030427 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : term38 A N t) (h2 : s = (@EMPTY (cart A M))) : True = ((term35 A M N s t) = (term45 A M N s t)).
Proof. exact (SYM (@lem8030426 A M N t s h1 h2)). Qed.
Lemma lem8030428 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : term38 A N t) (h2 : s = (@EMPTY (cart A M))) : (term35 A M N s t) = (term45 A M N s t).
Proof. exact (EQ_MP (@lem8030427 A M N t s h1 h2) (@lem0)). Qed.
Lemma lem8030429 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem8030435 {_141980 _141981 _141982 : Type'} : term50 _141980 _141981 _141982.
Proof. exact (proj1 (@lem8005965 _141980 _141981 _141982 Prop Prop Prop)). Qed.
Lemma lem8030436 {_141980 _141981 _141982 : Type'} (s : type24 _141980 _141981) : term51 _141980 _141981 _141982 s.
Proof. exact (@lem8030435 _141980 _141981 _141982 s). Qed.
Lemma lem8030437 {_141980 _141981 _141982 : Type'} (s : type24 _141980 _141981) : (term51 _141980 _141981 _141982 s) = ((@PCROSS _141980 _141981 _141982 s (@EMPTY (cart _141980 _141982))) = (@EMPTY (cart _141980 (finite_sum _141981 _141982)))).
Proof. exact (eq_refl (term51 _141980 _141981 _141982 s)). Qed.
Lemma lem8030439 {A M : Type'} (s : type24 A M) : term46 A M s.
Proof. exact (@lem82 (s = (@EMPTY (cart A M)))). Qed.
Lemma lem8030455 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : t = (@EMPTY (cart A N)).
Proof. exact (h1). Qed.
Lemma lem8030456 {A M N : Type'} (s : type24 A M) : (@PCROSS A M N s) = (@PCROSS A M N s).
Proof. exact (eq_refl (@PCROSS A M N s)). Qed.
Lemma lem8030457 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (@PCROSS A M N s t) = (@PCROSS A M N s (@EMPTY (cart A N))).
Proof. exact (MK_COMB (@lem8030456 A M N s) (@lem8030455 A N t h1)). Qed.
Lemma lem8030459 {_141980 _141981 _141982 : Type'} (s : type24 _141980 _141981) : (@PCROSS _141980 _141981 _141982 s (@EMPTY (cart _141980 _141982))) = (@EMPTY (cart _141980 (finite_sum _141981 _141982))).
Proof. exact (EQ_MP (@lem8030437 _141980 _141981 _141982 s) (@lem8030436 _141980 _141981 _141982 s)). Qed.
Lemma lem8030460 {A M N : Type'} (s : type24 A M) : (@PCROSS A M N s (@EMPTY (cart A N))) = (@EMPTY (cart A (finite_sum M N))).
Proof. exact (@lem8030459 A M N s). Qed.
Lemma lem8030461 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (@PCROSS A M N s t) = (@EMPTY (cart A (finite_sum M N))).
Proof. exact (TRANS (@lem8030457 A M N s t h1) (@lem8030460 A M N s)). Qed.
Lemma lem8030462 {A M N : Type'} : (@FINITE (cart A (finite_sum M N))) = (@FINITE (cart A (finite_sum M N))).
Proof. exact (eq_refl (@FINITE (cart A (finite_sum M N)))). Qed.
Lemma lem8030463 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (term35 A M N s t) = (@FINITE (cart A (finite_sum M N)) (@EMPTY (cart A (finite_sum M N)))).
Proof. exact (MK_COMB (@lem8030462 A M N) (@lem8030461 A M N s t h1)). Qed.
Lemma lem8030465 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem8030429 _92140) (@lem3596285 _92140)). Qed.
Lemma lem8030466 {A M N : Type'} : (@FINITE (cart A (finite_sum M N)) (@EMPTY (cart A (finite_sum M N)))) = True.
Proof. exact (@lem8030465 (type2 A M N)). Qed.
Lemma lem8030467 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (term35 A M N s t) = True.
Proof. exact (TRANS (@lem8030463 A M N s t h1) (@lem8030466 A M N)). Qed.
Lemma lem8030468 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8030469 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (term41 A M N s t) = (@eq Prop True).
Proof. exact (MK_COMB (@lem8030468) (@lem8030467 A M N s t h1)). Qed.
Lemma lem8030473 {A M : Type'} (s : type24 A M) (h1 : term38 A M s) : (s = (@EMPTY (cart A M))) = False.
Proof. exact (@lem8030439 A M s (@lem8030214 A M s h1)). Qed.
Lemma lem8030474 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8030475 {A M : Type'} (s : type24 A M) (h1 : term38 A M s) : (term42 A M s) = (or False).
Proof. exact (MK_COMB (@lem8030474) (@lem8030473 A M s h1)). Qed.
Lemma lem8030481 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : t = (@EMPTY (cart A N)).
Proof. exact (h1). Qed.
Lemma lem8030482 {A N : Type'} : (@eq ((cart A N) -> Prop)) = (@eq ((cart A N) -> Prop)).
Proof. exact (eq_refl (@eq ((cart A N) -> Prop))). Qed.
Lemma lem8030483 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (@eq ((cart A N) -> Prop) t) = (@eq ((cart A N) -> Prop) (@EMPTY (cart A N))).
Proof. exact (MK_COMB (@lem8030482 A N) (@lem8030481 A N t h1)). Qed.
Lemma lem8030484 {A N : Type'} : (@EMPTY (cart A N)) = (@EMPTY (cart A N)).
Proof. exact (eq_refl (@EMPTY (cart A N))). Qed.
Lemma lem8030485 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (t = (@EMPTY (cart A N))) = ((@EMPTY (cart A N)) = (@EMPTY (cart A N))).
Proof. exact (MK_COMB (@lem8030483 A N t h1) (@lem8030484 A N)). Qed.
Lemma lem8030487 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8030488 {A N : Type'} (x : type24 A N) : (x = x) = True.
Proof. exact (@lem8030487 (type24 A N) x). Qed.
Lemma lem8030489 {A N : Type'} : ((@EMPTY (cart A N)) = (@EMPTY (cart A N))) = True.
Proof. exact (@lem8030488 A N (@EMPTY (cart A N))). Qed.
Lemma lem8030490 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (t = (@EMPTY (cart A N))) = True.
Proof. exact (TRANS (@lem8030485 A N t h1) (@lem8030489 A N)). Qed.
Lemma lem8030491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8030492 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (term42 A N t) = (or True).
Proof. exact (MK_COMB (@lem8030491) (@lem8030490 A N t h1)). Qed.
Lemma lem8030496 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : t = (@EMPTY (cart A N)).
Proof. exact (h1). Qed.
Lemma lem8030497 {A N : Type'} : (@FINITE (cart A N)) = (@FINITE (cart A N)).
Proof. exact (eq_refl (@FINITE (cart A N))). Qed.
Lemma lem8030498 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (@FINITE (cart A N) t) = (@FINITE (cart A N) (@EMPTY (cart A N))).
Proof. exact (MK_COMB (@lem8030497 A N) (@lem8030496 A N t h1)). Qed.
Lemma lem8030500 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem8030429 _92140) (@lem3596285 _92140)). Qed.
Lemma lem8030501 {A N : Type'} : (@FINITE (cart A N) (@EMPTY (cart A N))) = True.
Proof. exact (@lem8030500 (cart A N)). Qed.
Lemma lem8030502 {A N : Type'} (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (@FINITE (cart A N) t) = True.
Proof. exact (TRANS (@lem8030498 A N t h1) (@lem8030501 A N)). Qed.
Lemma lem8030503 {A M : Type'} (s : type24 A M) : (term43 A M s) = (term43 A M s).
Proof. exact (eq_refl (term43 A M s)). Qed.
Lemma lem8030504 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (term34 A M N s t) = (term52 A M s).
Proof. exact (MK_COMB (@lem8030503 A M s) (@lem8030502 A N t h1)). Qed.
Lemma lem8030506 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem8030507 {A M : Type'} (s : type24 A M) : (term52 A M s) = (@FINITE (cart A M) s).
Proof. exact (@lem8030506 (@FINITE (cart A M) s)). Qed.
Lemma lem8030508 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (term34 A M N s t) = (@FINITE (cart A M) s).
Proof. exact (TRANS (@lem8030504 A M N s t h1) (@lem8030507 A M s)). Qed.
Lemma lem8030509 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (term44 A M N s t) = (term49 A M s).
Proof. exact (MK_COMB (@lem8030492 A N t h1) (@lem8030508 A M N s t h1)). Qed.
Lemma lem8030511 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem8030512 {A M : Type'} (s : type24 A M) : (term49 A M s) = True.
Proof. exact (@lem8030511 (@FINITE (cart A M) s)). Qed.
Lemma lem8030513 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : t = (@EMPTY (cart A N))) : (term44 A M N s t) = True.
Proof. exact (TRANS (@lem8030509 A M N s t h1) (@lem8030512 A M s)). Qed.
Lemma lem8030514 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A M s) (h2 : t = (@EMPTY (cart A N))) : (term45 A M N s t) = (False \/ True).
Proof. exact (MK_COMB (@lem8030475 A M s h1) (@lem8030513 A M N s t h2)). Qed.
Lemma lem8030516 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem8030517 : (False \/ True) = True.
Proof. exact (@lem8030516 True). Qed.
Lemma lem8030518 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A M s) (h2 : t = (@EMPTY (cart A N))) : (term45 A M N s t) = True.
Proof. exact (TRANS (@lem8030514 A M N s t h1 h2) (@lem8030517)). Qed.
Lemma lem8030519 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A M s) (h2 : t = (@EMPTY (cart A N))) : ((term35 A M N s t) = (term45 A M N s t)) = (True = True).
Proof. exact (MK_COMB (@lem8030469 A M N s t h2) (@lem8030518 A M N s t h1 h2)). Qed.
Lemma lem8030521 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem8030522 : (True = True) = True.
Proof. exact (@lem8030521 True). Qed.
Lemma lem8030523 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A M s) (h2 : t = (@EMPTY (cart A N))) : ((term35 A M N s t) = (term45 A M N s t)) = True.
Proof. exact (TRANS (@lem8030519 A M N s t h1 h2) (@lem8030522)). Qed.
Lemma lem8030524 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A M s) (h2 : t = (@EMPTY (cart A N))) : True = ((term35 A M N s t) = (term45 A M N s t)).
Proof. exact (SYM (@lem8030523 A M N s t h1 h2)). Qed.
Lemma lem8030525 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A M s) (h2 : t = (@EMPTY (cart A N))) : (term35 A M N s t) = (term45 A M N s t).
Proof. exact (EQ_MP (@lem8030524 A M N s t h1 h2) (@lem0)). Qed.
Lemma lem8030536 {A M : Type'} (s : type24 A M) : term46 A M s.
Proof. exact (@lem82 (s = (@EMPTY (cart A M)))). Qed.
Lemma lem8030549 {A N : Type'} (t : type24 A N) : term46 A N t.
Proof. exact (@lem82 (t = (@EMPTY (cart A N)))). Qed.
Lemma lem8030567 {A M : Type'} (s : type24 A M) (h1 : term38 A M s) : (s = (@EMPTY (cart A M))) = False.
Proof. exact (@lem8030536 A M s (@lem8030214 A M s h1)). Qed.
Lemma lem8030568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8030569 {A M : Type'} (s : type24 A M) (h1 : term38 A M s) : (term42 A M s) = (or False).
Proof. exact (MK_COMB (@lem8030568) (@lem8030567 A M s h1)). Qed.
Lemma lem8030573 {A N : Type'} (t : type24 A N) (h1 : term38 A N t) : (t = (@EMPTY (cart A N))) = False.
Proof. exact (@lem8030549 A N t (@lem8030219 A N t h1)). Qed.
Lemma lem8030574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8030575 {A N : Type'} (t : type24 A N) (h1 : term38 A N t) : (term42 A N t) = (or False).
Proof. exact (MK_COMB (@lem8030574) (@lem8030573 A N t h1)). Qed.
Lemma lem8030578 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term34 A M N s t) = (term34 A M N s t).
Proof. exact (eq_refl (term34 A M N s t)). Qed.
Lemma lem8030579 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A N t) : (term44 A M N s t) = (term53 A M N s t).
Proof. exact (MK_COMB (@lem8030575 A N t h1) (@lem8030578 A M N s t)). Qed.
Lemma lem8030581 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem8030582 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term53 A M N s t) = (term34 A M N s t).
Proof. exact (@lem8030581 (term34 A M N s t)). Qed.
Lemma lem8030585 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A N t) : (term44 A M N s t) = (term34 A M N s t).
Proof. exact (TRANS (@lem8030579 A M N s t h1) (@lem8030582 A M N s t)). Qed.
Lemma lem8030586 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A M s) (h2 : term38 A N t) : (term45 A M N s t) = (term53 A M N s t).
Proof. exact (MK_COMB (@lem8030569 A M s h1) (@lem8030585 A M N s t h2)). Qed.
Lemma lem8030588 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem8030589 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term53 A M N s t) = (term34 A M N s t).
Proof. exact (@lem8030588 (term34 A M N s t)). Qed.
Lemma lem8030592 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A M s) (h2 : term38 A N t) : (term45 A M N s t) = (term34 A M N s t).
Proof. exact (TRANS (@lem8030586 A M N s t h1 h2) (@lem8030589 A M N s t)). Qed.
Lemma lem8030593 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term41 A M N s t) = (term41 A M N s t).
Proof. exact (eq_refl (term41 A M N s t)). Qed.
Lemma lem8030594 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A M s) (h2 : term38 A N t) : ((term35 A M N s t) = (term45 A M N s t)) = ((term35 A M N s t) = (term34 A M N s t)).
Proof. exact (MK_COMB (@lem8030593 A M N s t) (@lem8030592 A M N s t h1 h2)). Qed.
Lemma lem8030597 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A M s) (h2 : term38 A N t) : ((term35 A M N s t) = (term34 A M N s t)) = ((term35 A M N s t) = (term45 A M N s t)).
Proof. exact (SYM (@lem8030594 A M N s t h1 h2)). Qed.
Lemma lem8030644 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term54 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem8030645 (p : Prop) (q : Prop) (p' : Prop) : term55 p q p'.
Proof. exact (fun q' : Prop => @lem8030644 p q p' q'). Qed.
Lemma lem8030646 (p : Prop) (q : Prop) : term56 p q.
Proof. exact (fun p' : Prop => @lem8030645 p q p'). Qed.
Lemma lem8030647 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term57 A M N s t.
Proof. exact (@lem8030646 (term34 A M N s t) (term35 A M N s t)). Qed.
Lemma lem8030648 {A M N : Type'} (s : type24 A M) (t : type24 A N) (p' : Prop) : term58 A M N s t p'.
Proof. exact (@lem8030647 A M N s t p'). Qed.
Lemma lem8030649 {A M N : Type'} (s : type24 A M) (t : type24 A N) (p' : Prop) : (term58 A M N s t p') = (term59 A M N s t p').
Proof. exact (eq_refl (term58 A M N s t p')). Qed.
Lemma lem8030650 {A M N : Type'} (s : type24 A M) (t : type24 A N) (p' : Prop) : term59 A M N s t p'.
Proof. exact (EQ_MP (@lem8030649 A M N s t p') (@lem8030648 A M N s t p')). Qed.
Lemma lem8030651 {A M N : Type'} (s : type24 A M) (t : type24 A N) (p' : Prop) (q' : Prop) : term60 A M N s t p' q'.
Proof. exact (@lem8030650 A M N s t p' q'). Qed.
Lemma lem8030652 {A M N : Type'} (s : type24 A M) (t : type24 A N) (p' : Prop) (q' : Prop) : (term60 A M N s t p' q') = (term61 A M N s t p' q').
Proof. exact (eq_refl (term60 A M N s t p' q')). Qed.
Lemma lem8030653 {A M N : Type'} (s : type24 A M) (t : type24 A N) (p' : Prop) (q' : Prop) : term61 A M N s t p' q'.
Proof. exact (EQ_MP (@lem8030652 A M N s t p' q') (@lem8030651 A M N s t p' q')). Qed.
Lemma lem8030656 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term34 A M N s t) = (term34 A M N s t).
Proof. exact (eq_refl (term34 A M N s t)). Qed.
Lemma lem8030657 {A M N : Type'} (s : type24 A M) (t : type24 A N) (q' : Prop) : term62 A M N s t q'.
Proof. exact (@lem8030653 A M N s t (term34 A M N s t) q'). Qed.
Lemma lem8030658 {A M N : Type'} (s : type24 A M) (t : type24 A N) (q' : Prop) : term63 A M N s t q'.
Proof. exact (@lem8030657 A M N s t q' (@lem8030656 A M N s t)). Qed.
Lemma lem8030659 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term34 A M N s t) : term34 A M N s t.
Proof. exact (h1). Qed.
Lemma lem8030660 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term34 A M N s t) : @FINITE (cart A N) t.
Proof. exact (proj2 (@lem8030659 A M N s t h1)). Qed.
Lemma lem8030661 {A N : Type'} (t : type24 A N) : (@FINITE (cart A N) t) = ((@FINITE (cart A N) t) = True).
Proof. exact (@lem7 (@FINITE (cart A N) t)). Qed.
Lemma lem8030663 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term34 A M N s t) : @FINITE (cart A M) s.
Proof. exact (proj1 (@lem8030659 A M N s t h1)). Qed.
Lemma lem8030664 {A M : Type'} (s : type24 A M) : (@FINITE (cart A M) s) = ((@FINITE (cart A M) s) = True).
Proof. exact (@lem7 (@FINITE (cart A M) s)). Qed.
Lemma lem8030667 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term64 A M N s t.
Proof. exact (fun h0 : term34 A M N s t => @lem8030204 A M N s t h0). Qed.
Lemma lem8030668 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term64 A M N s t.
Proof. exact (@lem8030667 A M N s t). Qed.
Lemma lem8030672 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term34 A M N s t) : (@FINITE (cart A M) s) = True.
Proof. exact (EQ_MP (@lem8030664 A M s) (@lem8030663 A M N s t h1)). Qed.
Lemma lem8030673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8030674 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term34 A M N s t) : (term43 A M s) = (and True).
Proof. exact (MK_COMB (@lem8030673) (@lem8030672 A M N s t h1)). Qed.
Lemma lem8030676 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term34 A M N s t) : (@FINITE (cart A N) t) = True.
Proof. exact (EQ_MP (@lem8030661 A N t) (@lem8030660 A M N s t h1)). Qed.
Lemma lem8030677 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term34 A M N s t) : (term34 A M N s t) = (True /\ True).
Proof. exact (MK_COMB (@lem8030674 A M N s t h1) (@lem8030676 A M N s t h1)). Qed.
Lemma lem8030679 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8030680 : (True /\ True) = True.
Proof. exact (@lem8030679 True). Qed.
Lemma lem8030681 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term34 A M N s t) : (term34 A M N s t) = True.
Proof. exact (TRANS (@lem8030677 A M N s t h1) (@lem8030680)). Qed.
Lemma lem8030682 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term34 A M N s t) : True = (term34 A M N s t).
Proof. exact (SYM (@lem8030681 A M N s t h1)). Qed.
Lemma lem8030683 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term34 A M N s t) : term34 A M N s t.
Proof. exact (EQ_MP (@lem8030682 A M N s t h1) (@lem0)). Qed.
Lemma lem8030684 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term34 A M N s t) : (term35 A M N s t) = True.
Proof. exact (@lem8030668 A M N s t (@lem8030683 A M N s t h1)). Qed.
Lemma lem8030685 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term64 A M N s t.
Proof. exact (fun h0 : term34 A M N s t => @lem8030684 A M N s t h0). Qed.
Lemma lem8030686 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term65 A M N s t.
Proof. exact (@lem8030658 A M N s t True). Qed.
Lemma lem8030687 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term33 A M N s t) = (term66 A M N s t).
Proof. exact (@lem8030686 A M N s t (@lem8030685 A M N s t)). Qed.
Lemma lem8030689 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8030690 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term66 A M N s t) = True.
Proof. exact (@lem8030689 (term34 A M N s t)). Qed.
Lemma lem8030691 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term33 A M N s t) = True.
Proof. exact (TRANS (@lem8030687 A M N s t) (@lem8030690 A M N s t)). Qed.
Lemma lem8030692 {A M N : Type'} (s : type24 A M) (t : type24 A N) : True = (term33 A M N s t).
Proof. exact (SYM (@lem8030691 A M N s t)). Qed.
Lemma lem8030693 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term33 A M N s t.
Proof. exact (EQ_MP (@lem8030692 A M N s t) (@lem0)). Qed.
Lemma lem8030694 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : term35 A M N s t.
Proof. exact (h1). Qed.
Lemma lem8030696 {A : Type'} (s : A -> Prop) : term26 A s.
Proof. exact (EQ_MP (@lem8030193 A s) (@lem8030192 A s)). Qed.
Lemma lem8030697 {A M : Type'} (s : type24 A M) : term67 A M s.
Proof. exact (@lem8030696 (cart A M) s). Qed.
Lemma lem8030699 {A : Type'} (s : A -> Prop) : term26 A s.
Proof. exact (EQ_MP (@lem8030193 A s) (@lem8030192 A s)). Qed.
Lemma lem8030700 {A N : Type'} (s : type24 A N) : term67 A N s.
Proof. exact (@lem8030699 (cart A N) s). Qed.
Lemma lem8030701 {A N : Type'} (t : type24 A N) : term67 A N t.
Proof. exact (@lem8030700 A N t). Qed.
Lemma lem8030702 {A B : Type'} (y : B) : term68 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem8030703 {A B : Type'} (y : B) : (term68 A B y) = (term69 A B y).
Proof. exact (eq_refl (term68 A B y)). Qed.
Lemma lem8030704 {A B : Type'} (y : B) : term69 A B y.
Proof. exact (EQ_MP (@lem8030703 A B y) (@lem8030702 A B y)). Qed.
Lemma lem8030705 {A B : Type'} (y : B) (s : A -> Prop) : term70 A B y s.
Proof. exact (@lem8030704 A B y s). Qed.
Lemma lem8030706 {A B : Type'} (y : B) (s : A -> Prop) : (term70 A B y s) = (term71 A B y s).
Proof. exact (eq_refl (term70 A B y s)). Qed.
Lemma lem8030707 {A B : Type'} (y : B) (s : A -> Prop) : term71 A B y s.
Proof. exact (EQ_MP (@lem8030706 A B y s) (@lem8030705 A B y s)). Qed.
Lemma lem8030708 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term72 A B y s f.
Proof. exact (@lem8030707 A B y s f). Qed.
Lemma lem8030709 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term72 A B y s f) = ((term73 A B y f s) = (term74 A B y f s)).
Proof. exact (eq_refl (term72 A B y s f)). Qed.
Lemma lem8030711 {A : Type'} (s : A -> Prop) : term75 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem8030712 {A : Type'} (s : A -> Prop) : (term75 A s) = (term76 A s).
Proof. exact (eq_refl (term75 A s)). Qed.
Lemma lem8030713 {A : Type'} (s : A -> Prop) : term76 A s.
Proof. exact (EQ_MP (@lem8030712 A s) (@lem8030711 A s)). Qed.
Lemma lem8030714 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term77 A s t.
Proof. exact (@lem8030713 A s t). Qed.
Lemma lem8030715 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term77 A s t) = ((@SUBSET A s t) = (term78 A s t)).
Proof. exact (eq_refl (term77 A s t)). Qed.
Lemma lem8030717 {A B : Type'} (f : A -> B) : term79 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem8030718 {A B : Type'} (f : A -> B) : (term79 A B f) = (term80 A B f).
Proof. exact (eq_refl (term79 A B f)). Qed.
Lemma lem8030719 {A B : Type'} (f : A -> B) : term80 A B f.
Proof. exact (EQ_MP (@lem8030718 A B f) (@lem8030717 A B f)). Qed.
Lemma lem8030720 {A B : Type'} (f : A -> B) (s : A -> Prop) : term81 A B f s.
Proof. exact (@lem8030719 A B f s). Qed.
Lemma lem8030721 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term81 A B f s) = (term82 A B f s).
Proof. exact (eq_refl (term81 A B f s)). Qed.
Lemma lem8030722 {A B : Type'} (f : A -> B) (s : A -> Prop) : term82 A B f s.
Proof. exact (EQ_MP (@lem8030721 A B f s) (@lem8030720 A B f s)). Qed.
Lemma lem8030723 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem8030724 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term83 A B f s.
Proof. exact (@lem8030722 A B f s (@lem8030723 A s h1)). Qed.
Lemma lem8030725 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term83 A B f s) = ((term83 A B f s) = True).
Proof. exact (@lem7 (term83 A B f s)). Qed.
Lemma lem8030726 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term83 A B f s) = True.
Proof. exact (EQ_MP (@lem8030725 A B f s) (@lem8030724 A B f s h1)). Qed.
Lemma lem8030758 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term35 A M N s t) = ((term35 A M N s t) = True).
Proof. exact (@lem7 (term35 A M N s t)). Qed.
Lemma lem8030763 {A B : Type'} (f : A -> B) (s : A -> Prop) : term84 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem8030726 A B f s h0). Qed.
Lemma lem8030764 {A M N : Type'} (f : type13 A M N) (s : type16 A M N) : term85 A M N f s.
Proof. exact (@lem8030763 (type2 A M N) (cart A M) f s). Qed.
Lemma lem8030765 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term86 A M N s t.
Proof. exact (@lem8030764 A M N (@fstcart A M N) (@PCROSS A M N s t)). Qed.
Lemma lem8030767 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : (term35 A M N s t) = True.
Proof. exact (EQ_MP (@lem8030758 A M N s t) (@lem8030694 A M N s t h1)). Qed.
Lemma lem8030768 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : True = (term35 A M N s t).
Proof. exact (SYM (@lem8030767 A M N s t h1)). Qed.
Lemma lem8030769 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : term35 A M N s t.
Proof. exact (EQ_MP (@lem8030768 A M N s t h1) (@lem0)). Qed.
Lemma lem8030770 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : (term87 A M N s t) = True.
Proof. exact (@lem8030765 A M N s t (@lem8030769 A M N s t h1)). Qed.
Lemma lem8030771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8030772 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : (term88 A M N s t) = (and True).
Proof. exact (MK_COMB (@lem8030771) (@lem8030770 A M N s t h1)). Qed.
Lemma lem8030774 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term78 A s t).
Proof. exact (EQ_MP (@lem8030715 A s t) (@lem8030714 A s t)). Qed.
Lemma lem8030775 {A M : Type'} (s : type24 A M) (t : type24 A M) : (@SUBSET (cart A M) s t) = (term89 A M s t).
Proof. exact (@lem8030774 (cart A M) s t). Qed.
Lemma lem8030776 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term90 A M N s t) = (term91 A M N s t).
Proof. exact (@lem8030775 A M s (term92 A M N s t)). Qed.
Lemma lem8030784 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term54 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem8030785 (p : Prop) (q : Prop) (p' : Prop) : term55 p q p'.
Proof. exact (fun q' : Prop => @lem8030784 p q p' q'). Qed.
Lemma lem8030786 (p : Prop) (q : Prop) : term56 p q.
Proof. exact (fun p' : Prop => @lem8030785 p q p'). Qed.
Lemma lem8030787 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : term93 A M N x s t.
Proof. exact (@lem8030786 (@IN (cart A M) x s) (term94 A M N x s t)). Qed.
Lemma lem8030788 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) (p' : Prop) : term95 A M N x s t p'.
Proof. exact (@lem8030787 A M N x s t p'). Qed.
Lemma lem8030789 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) (p' : Prop) : (term95 A M N x s t p') = (term96 A M N x s t p').
Proof. exact (eq_refl (term95 A M N x s t p')). Qed.
Lemma lem8030790 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) (p' : Prop) : term96 A M N x s t p'.
Proof. exact (EQ_MP (@lem8030789 A M N x s t p') (@lem8030788 A M N x s t p')). Qed.
Lemma lem8030791 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) (p' : Prop) (q' : Prop) : term97 A M N x s t p' q'.
Proof. exact (@lem8030790 A M N x s t p' q'). Qed.
Lemma lem8030792 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) (p' : Prop) (q' : Prop) : (term97 A M N x s t p' q') = (term98 A M N x s t p' q').
Proof. exact (eq_refl (term97 A M N x s t p' q')). Qed.
Lemma lem8030793 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) (p' : Prop) (q' : Prop) : term98 A M N x s t p' q'.
Proof. exact (EQ_MP (@lem8030792 A M N x s t p' q') (@lem8030791 A M N x s t p' q')). Qed.
Lemma lem8030794 {A M : Type'} (x : cart A M) (s : type24 A M) : (@IN (cart A M) x s) = (@IN (cart A M) x s).
Proof. exact (eq_refl (@IN (cart A M) x s)). Qed.
Lemma lem8030795 {A M N : Type'} (t : type24 A N) (x : cart A M) (s : type24 A M) (q' : Prop) : term99 A M N t x s q'.
Proof. exact (@lem8030793 A M N x s t (@IN (cart A M) x s) q'). Qed.
Lemma lem8030796 {A M N : Type'} (t : type24 A N) (x : cart A M) (s : type24 A M) (q' : Prop) : term100 A M N t x s q'.
Proof. exact (@lem8030795 A M N t x s q' (@lem8030794 A M x s)). Qed.
Lemma lem8030801 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term73 A B y f s) = (term74 A B y f s).
Proof. exact (EQ_MP (@lem8030709 A B y f s) (@lem8030708 A B y s f)). Qed.
Lemma lem8030802 {A M N : Type'} (y : cart A M) (f : type13 A M N) (s : type16 A M N) : (term101 A M N y f s) = (term102 A M N y f s).
Proof. exact (@lem8030801 (type2 A M N) (cart A M) y f s). Qed.
Lemma lem8030803 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term94 A M N x s t) = (term103 A M N x s t).
Proof. exact (@lem8030802 A M N x (@fstcart A M N) (@PCROSS A M N s t)). Qed.
Lemma lem8030809 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term104 _140476 _140477 _140478 P) = (term105 _140476 _140477 _140478 P).
Proof. exact (EQ_MP (@lem7662554 _140476 _140477 _140478 P) (@lem7664352 _140476 _140477 _140478 P)). Qed.
Lemma lem8030810 {A M N : Type'} (P : type16 A M N) : (term104 A M N P) = (term105 A M N P).
Proof. exact (@lem8030809 A M N P). Qed.
Lemma lem8030811 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term106 A M N x s t) = (term107 A M N x s t).
Proof. exact (@lem8030810 A M N (term108 A M N x s t)). Qed.
Lemma lem8030812 {A M N : Type'} (x : cart A M) (x' : type2 A M N) (s : type24 A M) (t : type24 A N) : (term109 A M N x s t x') = (term110 A M N x x' s t).
Proof. exact (eq_refl (term109 A M N x s t x')). Qed.
Lemma lem8030813 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term111 A M N x s t) = (term108 A M N x s t).
Proof. exact (fun_ext (fun x' : type2 A M N => @lem8030812 A M N x x' s t)). Qed.
Lemma lem8030814 {A M N : Type'} : (@ex (cart A (finite_sum M N))) = (@ex (cart A (finite_sum M N))).
Proof. exact (eq_refl (@ex (cart A (finite_sum M N)))). Qed.
Lemma lem8030815 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term106 A M N x s t) = (term103 A M N x s t).
Proof. exact (MK_COMB (@lem8030814 A M N) (@lem8030813 A M N x s t)). Qed.
Lemma lem8030816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8030817 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term112 A M N x s t) = (term113 A M N x s t).
Proof. exact (MK_COMB (@lem8030816) (@lem8030815 A M N x s t)). Qed.
Lemma lem8030818 {A M N : Type'} (x : cart A M) (x' : cart A M) (y : cart A N) (s : type24 A M) (t : type24 A N) : (term114 A M N x s t x' y) = (term115 A M N x x' y s t).
Proof. exact (eq_refl (term114 A M N x s t x' y)). Qed.
Lemma lem8030819 {A M N : Type'} (x : cart A M) (x' : cart A M) (s : type24 A M) (t : type24 A N) : (term116 A M N x s t x') = (term117 A M N x x' s t).
Proof. exact (fun_ext (fun y : cart A N => @lem8030818 A M N x x' y s t)). Qed.
Lemma lem8030820 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8030821 {A M N : Type'} (x : cart A M) (x' : cart A M) (s : type24 A M) (t : type24 A N) : (term118 A M N x s t x') = (term119 A M N x x' s t).
Proof. exact (MK_COMB (@lem8030820 A N) (@lem8030819 A M N x x' s t)). Qed.
Lemma lem8030822 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term120 A M N x s t) = (term121 A M N x s t).
Proof. exact (fun_ext (fun x' : cart A M => @lem8030821 A M N x x' s t)). Qed.
Lemma lem8030823 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8030824 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term107 A M N x s t) = (term122 A M N x s t).
Proof. exact (MK_COMB (@lem8030823 A M) (@lem8030822 A M N x s t)). Qed.
Lemma lem8030825 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : ((term106 A M N x s t) = (term107 A M N x s t)) = ((term103 A M N x s t) = (term122 A M N x s t)).
Proof. exact (MK_COMB (@lem8030817 A M N x s t) (@lem8030824 A M N x s t)). Qed.
Lemma lem8030826 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term103 A M N x s t) = (term122 A M N x s t).
Proof. exact (EQ_MP (@lem8030825 A M N x s t) (@lem8030811 A M N x s t)). Qed.
Lemma lem8030843 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term94 A M N x s t) = (term122 A M N x s t).
Proof. exact (TRANS (@lem8030803 A M N x s t) (@lem8030826 A M N x s t)). Qed.
Lemma lem8030844 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : term123 A M N x s t.
Proof. exact (fun h0 : @IN (cart A M) x s => @lem8030843 A M N x s t). Qed.
Lemma lem8030845 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : term124 A M N x s t.
Proof. exact (@lem8030796 A M N t x s (term122 A M N x s t)). Qed.
Lemma lem8030846 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term125 A M N x s t) = (term126 A M N x s t).
Proof. exact (@lem8030845 A M N x s t (@lem8030844 A M N x s t)). Qed.
Lemma lem8030902 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term127 A M N s t) = (term128 A M N s t).
Proof. exact (fun_ext (fun x : cart A M => @lem8030846 A M N x s t)). Qed.
Lemma lem8030958 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8030959 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term91 A M N s t) = (term129 A M N s t).
Proof. exact (MK_COMB (@lem8030958 A M) (@lem8030902 A M N s t)). Qed.
Lemma lem8031019 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term90 A M N s t) = (term129 A M N s t).
Proof. exact (TRANS (@lem8030776 A M N s t) (@lem8030959 A M N s t)). Qed.
Lemma lem8031020 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : (term130 A M N s t) = (term131 A M N s t).
Proof. exact (MK_COMB (@lem8030772 A M N s t h1) (@lem8031019 A M N s t)). Qed.
Lemma lem8031022 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8031023 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term131 A M N s t) = (term129 A M N s t).
Proof. exact (@lem8031022 (term129 A M N s t)). Qed.
Lemma lem8031083 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : (term130 A M N s t) = (term129 A M N s t).
Proof. exact (TRANS (@lem8031020 A M N s t h1) (@lem8031023 A M N s t)). Qed.
Lemma lem8031084 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : (term129 A M N s t) = (term130 A M N s t).
Proof. exact (SYM (@lem8031083 A M N s t h1)). Qed.
Lemma lem8031085 {A B : Type'} (y : B) : term68 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem8031086 {A B : Type'} (y : B) : (term68 A B y) = (term69 A B y).
Proof. exact (eq_refl (term68 A B y)). Qed.
Lemma lem8031087 {A B : Type'} (y : B) : term69 A B y.
Proof. exact (EQ_MP (@lem8031086 A B y) (@lem8031085 A B y)). Qed.
Lemma lem8031088 {A B : Type'} (y : B) (s : A -> Prop) : term70 A B y s.
Proof. exact (@lem8031087 A B y s). Qed.
Lemma lem8031089 {A B : Type'} (y : B) (s : A -> Prop) : (term70 A B y s) = (term71 A B y s).
Proof. exact (eq_refl (term70 A B y s)). Qed.
Lemma lem8031090 {A B : Type'} (y : B) (s : A -> Prop) : term71 A B y s.
Proof. exact (EQ_MP (@lem8031089 A B y s) (@lem8031088 A B y s)). Qed.
Lemma lem8031091 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term72 A B y s f.
Proof. exact (@lem8031090 A B y s f). Qed.
Lemma lem8031092 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term72 A B y s f) = ((term73 A B y f s) = (term74 A B y f s)).
Proof. exact (eq_refl (term72 A B y s f)). Qed.
Lemma lem8031094 {A : Type'} (s : A -> Prop) : term75 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem8031095 {A : Type'} (s : A -> Prop) : (term75 A s) = (term76 A s).
Proof. exact (eq_refl (term75 A s)). Qed.
Lemma lem8031096 {A : Type'} (s : A -> Prop) : term76 A s.
Proof. exact (EQ_MP (@lem8031095 A s) (@lem8031094 A s)). Qed.
Lemma lem8031097 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term77 A s t.
Proof. exact (@lem8031096 A s t). Qed.
Lemma lem8031098 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term77 A s t) = ((@SUBSET A s t) = (term78 A s t)).
Proof. exact (eq_refl (term77 A s t)). Qed.
Lemma lem8031100 {A B : Type'} (f : A -> B) : term79 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem8031101 {A B : Type'} (f : A -> B) : (term79 A B f) = (term80 A B f).
Proof. exact (eq_refl (term79 A B f)). Qed.
Lemma lem8031102 {A B : Type'} (f : A -> B) : term80 A B f.
Proof. exact (EQ_MP (@lem8031101 A B f) (@lem8031100 A B f)). Qed.
Lemma lem8031103 {A B : Type'} (f : A -> B) (s : A -> Prop) : term81 A B f s.
Proof. exact (@lem8031102 A B f s). Qed.
Lemma lem8031104 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term81 A B f s) = (term82 A B f s).
Proof. exact (eq_refl (term81 A B f s)). Qed.
Lemma lem8031105 {A B : Type'} (f : A -> B) (s : A -> Prop) : term82 A B f s.
Proof. exact (EQ_MP (@lem8031104 A B f s) (@lem8031103 A B f s)). Qed.
Lemma lem8031106 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem8031107 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term83 A B f s.
Proof. exact (@lem8031105 A B f s (@lem8031106 A s h1)). Qed.
Lemma lem8031108 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term83 A B f s) = ((term83 A B f s) = True).
Proof. exact (@lem7 (term83 A B f s)). Qed.
Lemma lem8031109 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term83 A B f s) = True.
Proof. exact (EQ_MP (@lem8031108 A B f s) (@lem8031107 A B f s h1)). Qed.
Lemma lem8031141 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term35 A M N s t) = ((term35 A M N s t) = True).
Proof. exact (@lem7 (term35 A M N s t)). Qed.
Lemma lem8031146 {A B : Type'} (f : A -> B) (s : A -> Prop) : term84 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem8031109 A B f s h0). Qed.
Lemma lem8031147 {A M N : Type'} (f : type14 A M N) (s : type16 A M N) : term132 A M N f s.
Proof. exact (@lem8031146 (type2 A M N) (cart A N) f s). Qed.
Lemma lem8031148 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term133 A M N s t.
Proof. exact (@lem8031147 A M N (@sndcart A M N) (@PCROSS A M N s t)). Qed.
Lemma lem8031150 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : (term35 A M N s t) = True.
Proof. exact (EQ_MP (@lem8031141 A M N s t) (@lem8030694 A M N s t h1)). Qed.
Lemma lem8031151 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : True = (term35 A M N s t).
Proof. exact (SYM (@lem8031150 A M N s t h1)). Qed.
Lemma lem8031152 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : term35 A M N s t.
Proof. exact (EQ_MP (@lem8031151 A M N s t h1) (@lem0)). Qed.
Lemma lem8031153 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : (term134 A M N s t) = True.
Proof. exact (@lem8031148 A M N s t (@lem8031152 A M N s t h1)). Qed.
Lemma lem8031154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8031155 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : (term135 A M N s t) = (and True).
Proof. exact (MK_COMB (@lem8031154) (@lem8031153 A M N s t h1)). Qed.
Lemma lem8031157 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term78 A s t).
Proof. exact (EQ_MP (@lem8031098 A s t) (@lem8031097 A s t)). Qed.
Lemma lem8031158 {A N : Type'} (s : type24 A N) (t : type24 A N) : (@SUBSET (cart A N) s t) = (term89 A N s t).
Proof. exact (@lem8031157 (cart A N) s t). Qed.
Lemma lem8031159 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term136 A M N s t) = (term137 A M N s t).
Proof. exact (@lem8031158 A N t (term138 A M N s t)). Qed.
Lemma lem8031167 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term54 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem8031168 (p : Prop) (q : Prop) (p' : Prop) : term55 p q p'.
Proof. exact (fun q' : Prop => @lem8031167 p q p' q'). Qed.
Lemma lem8031169 (p : Prop) (q : Prop) : term56 p q.
Proof. exact (fun p' : Prop => @lem8031168 p q p'). Qed.
Lemma lem8031170 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : term139 A M N x s t.
Proof. exact (@lem8031169 (@IN (cart A N) x t) (term140 A M N x s t)). Qed.
Lemma lem8031171 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) (p' : Prop) : term141 A M N x s t p'.
Proof. exact (@lem8031170 A M N x s t p'). Qed.
Lemma lem8031172 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) (p' : Prop) : (term141 A M N x s t p') = (term142 A M N x s t p').
Proof. exact (eq_refl (term141 A M N x s t p')). Qed.
Lemma lem8031173 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) (p' : Prop) : term142 A M N x s t p'.
Proof. exact (EQ_MP (@lem8031172 A M N x s t p') (@lem8031171 A M N x s t p')). Qed.
Lemma lem8031174 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) (p' : Prop) (q' : Prop) : term143 A M N x s t p' q'.
Proof. exact (@lem8031173 A M N x s t p' q'). Qed.
Lemma lem8031175 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) (p' : Prop) (q' : Prop) : (term143 A M N x s t p' q') = (term144 A M N x s t p' q').
Proof. exact (eq_refl (term143 A M N x s t p' q')). Qed.
Lemma lem8031176 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) (p' : Prop) (q' : Prop) : term144 A M N x s t p' q'.
Proof. exact (EQ_MP (@lem8031175 A M N x s t p' q') (@lem8031174 A M N x s t p' q')). Qed.
Lemma lem8031177 {A N : Type'} (x : cart A N) (t : type24 A N) : (@IN (cart A N) x t) = (@IN (cart A N) x t).
Proof. exact (eq_refl (@IN (cart A N) x t)). Qed.
Lemma lem8031178 {A M N : Type'} (s : type24 A M) (x : cart A N) (t : type24 A N) (q' : Prop) : term145 A M N s x t q'.
Proof. exact (@lem8031176 A M N x s t (@IN (cart A N) x t) q'). Qed.
Lemma lem8031179 {A M N : Type'} (s : type24 A M) (x : cart A N) (t : type24 A N) (q' : Prop) : term146 A M N s x t q'.
Proof. exact (@lem8031178 A M N s x t q' (@lem8031177 A N x t)). Qed.
Lemma lem8031184 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term73 A B y f s) = (term74 A B y f s).
Proof. exact (EQ_MP (@lem8031092 A B y f s) (@lem8031091 A B y s f)). Qed.
Lemma lem8031185 {A M N : Type'} (y : cart A N) (f : type14 A M N) (s : type16 A M N) : (term147 A M N y f s) = (term148 A M N y f s).
Proof. exact (@lem8031184 (type2 A M N) (cart A N) y f s). Qed.
Lemma lem8031186 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term140 A M N x s t) = (term149 A M N x s t).
Proof. exact (@lem8031185 A M N x (@sndcart A M N) (@PCROSS A M N s t)). Qed.
Lemma lem8031192 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term104 _140476 _140477 _140478 P) = (term105 _140476 _140477 _140478 P).
Proof. exact (EQ_MP (@lem7662554 _140476 _140477 _140478 P) (@lem7664352 _140476 _140477 _140478 P)). Qed.
Lemma lem8031193 {A M N : Type'} (P : type16 A M N) : (term104 A M N P) = (term105 A M N P).
Proof. exact (@lem8031192 A M N P). Qed.
Lemma lem8031194 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term150 A M N x s t) = (term151 A M N x s t).
Proof. exact (@lem8031193 A M N (term152 A M N x s t)). Qed.
Lemma lem8031195 {A M N : Type'} (x : cart A N) (x' : type2 A M N) (s : type24 A M) (t : type24 A N) : (term153 A M N x s t x') = (term154 A M N x x' s t).
Proof. exact (eq_refl (term153 A M N x s t x')). Qed.
Lemma lem8031196 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term155 A M N x s t) = (term152 A M N x s t).
Proof. exact (fun_ext (fun x' : type2 A M N => @lem8031195 A M N x x' s t)). Qed.
Lemma lem8031197 {A M N : Type'} : (@ex (cart A (finite_sum M N))) = (@ex (cart A (finite_sum M N))).
Proof. exact (eq_refl (@ex (cart A (finite_sum M N)))). Qed.
Lemma lem8031198 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term150 A M N x s t) = (term149 A M N x s t).
Proof. exact (MK_COMB (@lem8031197 A M N) (@lem8031196 A M N x s t)). Qed.
Lemma lem8031199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8031200 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term156 A M N x s t) = (term157 A M N x s t).
Proof. exact (MK_COMB (@lem8031199) (@lem8031198 A M N x s t)). Qed.
Lemma lem8031201 {A M N : Type'} (x : cart A N) (x' : cart A M) (y : cart A N) (s : type24 A M) (t : type24 A N) : (term158 A M N x s t x' y) = (term159 A M N x x' y s t).
Proof. exact (eq_refl (term158 A M N x s t x' y)). Qed.
Lemma lem8031202 {A M N : Type'} (x : cart A N) (x' : cart A M) (s : type24 A M) (t : type24 A N) : (term160 A M N x s t x') = (term161 A M N x x' s t).
Proof. exact (fun_ext (fun y : cart A N => @lem8031201 A M N x x' y s t)). Qed.
Lemma lem8031203 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8031204 {A M N : Type'} (x : cart A N) (x' : cart A M) (s : type24 A M) (t : type24 A N) : (term162 A M N x s t x') = (term163 A M N x x' s t).
Proof. exact (MK_COMB (@lem8031203 A N) (@lem8031202 A M N x x' s t)). Qed.
Lemma lem8031205 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term164 A M N x s t) = (term165 A M N x s t).
Proof. exact (fun_ext (fun x' : cart A M => @lem8031204 A M N x x' s t)). Qed.
Lemma lem8031206 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8031207 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term151 A M N x s t) = (term166 A M N x s t).
Proof. exact (MK_COMB (@lem8031206 A M) (@lem8031205 A M N x s t)). Qed.
Lemma lem8031208 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : ((term150 A M N x s t) = (term151 A M N x s t)) = ((term149 A M N x s t) = (term166 A M N x s t)).
Proof. exact (MK_COMB (@lem8031200 A M N x s t) (@lem8031207 A M N x s t)). Qed.
Lemma lem8031209 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term149 A M N x s t) = (term166 A M N x s t).
Proof. exact (EQ_MP (@lem8031208 A M N x s t) (@lem8031194 A M N x s t)). Qed.
Lemma lem8031226 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term140 A M N x s t) = (term166 A M N x s t).
Proof. exact (TRANS (@lem8031186 A M N x s t) (@lem8031209 A M N x s t)). Qed.
Lemma lem8031227 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : term167 A M N x s t.
Proof. exact (fun h0 : @IN (cart A N) x t => @lem8031226 A M N x s t). Qed.
Lemma lem8031228 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : term168 A M N x s t.
Proof. exact (@lem8031179 A M N s x t (term166 A M N x s t)). Qed.
Lemma lem8031229 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term169 A M N x s t) = (term170 A M N x s t).
Proof. exact (@lem8031228 A M N x s t (@lem8031227 A M N x s t)). Qed.
Lemma lem8031285 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term171 A M N s t) = (term172 A M N s t).
Proof. exact (fun_ext (fun x : cart A N => @lem8031229 A M N x s t)). Qed.
Lemma lem8031341 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8031342 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term137 A M N s t) = (term173 A M N s t).
Proof. exact (MK_COMB (@lem8031341 A N) (@lem8031285 A M N s t)). Qed.
Lemma lem8031402 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term136 A M N s t) = (term173 A M N s t).
Proof. exact (TRANS (@lem8031159 A M N s t) (@lem8031342 A M N s t)). Qed.
Lemma lem8031403 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : (term174 A M N s t) = (term175 A M N s t).
Proof. exact (MK_COMB (@lem8031155 A M N s t h1) (@lem8031402 A M N s t)). Qed.
Lemma lem8031405 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8031406 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term175 A M N s t) = (term173 A M N s t).
Proof. exact (@lem8031405 (term173 A M N s t)). Qed.
Lemma lem8031466 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : (term174 A M N s t) = (term173 A M N s t).
Proof. exact (TRANS (@lem8031403 A M N s t h1) (@lem8031406 A M N s t)). Qed.
Lemma lem8031467 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) : (term173 A M N s t) = (term174 A M N s t).
Proof. exact (SYM (@lem8031466 A M N s t h1)). Qed.
Lemma lem8031487 {A M N : Type'} (y : cart A N) (x : cart A M) : (term7 A M N x y) = x.
Proof. exact (EQ_MP (@lem8030160 A M N y x) (@lem8030159 A M N x y)). Qed.
Lemma lem8031488 {A M N : Type'} (y : cart A N) (x : cart A M) : (term7 A M N x y) = x.
Proof. exact (@lem8031487 A M N y x). Qed.
Lemma lem8031489 {A M N : Type'} (y : cart A N) (x' : cart A M) : (term7 A M N x' y) = x'.
Proof. exact (@lem8031488 A M N y x'). Qed.
Lemma lem8031490 {A M : Type'} (x : cart A M) : (@eq (cart A M) x) = (@eq (cart A M) x).
Proof. exact (eq_refl (@eq (cart A M) x)). Qed.
Lemma lem8031491 {A M N : Type'} (y : cart A N) (x : cart A M) (x' : cart A M) : (x = (term7 A M N x' y)) = (x = x').
Proof. exact (MK_COMB (@lem8031490 A M x) (@lem8031489 A M N y x')). Qed.
Lemma lem8031494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8031495 {A M N : Type'} (y : cart A N) (x : cart A M) (x' : cart A M) : (term176 A M N x x' y) = (term177 A M x x').
Proof. exact (MK_COMB (@lem8031494) (@lem8031491 A M N y x x')). Qed.
Lemma lem8031497 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term15 _141927 _141928 _141929 x y s t) = (term16 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8030172 _141927 _141928 _141929 x s y t) (@lem8030171 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8031498 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term15 A M N x y s t) = (term16 A M N x s y t).
Proof. exact (@lem8031497 A M N x s y t). Qed.
Lemma lem8031499 {A M N : Type'} (x' : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term15 A M N x' y s t) = (term16 A M N x' s y t).
Proof. exact (@lem8031498 A M N x' s y t). Qed.
Lemma lem8031502 {A M N : Type'} (x : cart A M) (x' : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term115 A M N x x' y s t) = (term178 A M N x x' s y t).
Proof. exact (MK_COMB (@lem8031495 A M N y x x') (@lem8031499 A M N x' s y t)). Qed.
Lemma lem8031505 {A M N : Type'} (x : cart A M) (x' : cart A M) (s : type24 A M) (t : type24 A N) : (term117 A M N x x' s t) = (term179 A M N x x' s t).
Proof. exact (fun_ext (fun y : cart A N => @lem8031502 A M N x x' s y t)). Qed.
Lemma lem8031506 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8031507 {A M N : Type'} (x : cart A M) (x' : cart A M) (s : type24 A M) (t : type24 A N) : (term119 A M N x x' s t) = (term180 A M N x x' s t).
Proof. exact (MK_COMB (@lem8031506 A N) (@lem8031505 A M N x x' s t)). Qed.
Lemma lem8031512 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term121 A M N x s t) = (term181 A M N x s t).
Proof. exact (fun_ext (fun x' : cart A M => @lem8031507 A M N x x' s t)). Qed.
Lemma lem8031513 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8031514 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term122 A M N x s t) = (term182 A M N x s t).
Proof. exact (MK_COMB (@lem8031513 A M) (@lem8031512 A M N x s t)). Qed.
Lemma lem8031519 {A M : Type'} (x : cart A M) (s : type24 A M) : (term183 A M x s) = (term183 A M x s).
Proof. exact (eq_refl (term183 A M x s)). Qed.
Lemma lem8031520 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term126 A M N x s t) = (term184 A M N x s t).
Proof. exact (MK_COMB (@lem8031519 A M x s) (@lem8031514 A M N x s t)). Qed.
Lemma lem8031523 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term128 A M N s t) = (term185 A M N s t).
Proof. exact (fun_ext (fun x : cart A M => @lem8031520 A M N x s t)). Qed.
Lemma lem8031524 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8031525 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term129 A M N s t) = (term186 A M N s t).
Proof. exact (MK_COMB (@lem8031524 A M) (@lem8031523 A M N s t)). Qed.
Lemma lem8031530 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term186 A M N s t) = (term129 A M N s t).
Proof. exact (SYM (@lem8031525 A M N s t)). Qed.
Lemma lem8031550 {A M N : Type'} (x : cart A M) (y : cart A N) : (term3 A M N x y) = y.
Proof. exact (EQ_MP (@lem8030154 A M N x y) (@lem8030153 A M N x y)). Qed.
Lemma lem8031551 {A M N : Type'} (x : cart A M) (y : cart A N) : (term3 A M N x y) = y.
Proof. exact (@lem8031550 A M N x y). Qed.
Lemma lem8031552 {A N : Type'} (x : cart A N) : (@eq (cart A N) x) = (@eq (cart A N) x).
Proof. exact (eq_refl (@eq (cart A N) x)). Qed.
Lemma lem8031553 {A M N : Type'} (x : cart A M) (x' : cart A N) (y : cart A N) : (x' = (term3 A M N x y)) = (x' = y).
Proof. exact (MK_COMB (@lem8031552 A N x') (@lem8031551 A M N x y)). Qed.
Lemma lem8031556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8031557 {A M N : Type'} (x : cart A M) (x' : cart A N) (y : cart A N) : (term187 A M N x' x y) = (term177 A N x' y).
Proof. exact (MK_COMB (@lem8031556) (@lem8031553 A M N x x' y)). Qed.
Lemma lem8031559 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term15 _141927 _141928 _141929 x y s t) = (term16 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8030172 _141927 _141928 _141929 x s y t) (@lem8030171 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8031560 {A M N : Type'} (x : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term15 A M N x y s t) = (term16 A M N x s y t).
Proof. exact (@lem8031559 A M N x s y t). Qed.
Lemma lem8031563 {A M N : Type'} (x : cart A N) (x' : cart A M) (s : type24 A M) (y : cart A N) (t : type24 A N) : (term159 A M N x x' y s t) = (term188 A M N x x' s y t).
Proof. exact (MK_COMB (@lem8031557 A M N x' x y) (@lem8031560 A M N x' s y t)). Qed.
Lemma lem8031566 {A M N : Type'} (x : cart A N) (x' : cart A M) (s : type24 A M) (t : type24 A N) : (term161 A M N x x' s t) = (term189 A M N x x' s t).
Proof. exact (fun_ext (fun y : cart A N => @lem8031563 A M N x x' s y t)). Qed.
Lemma lem8031567 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8031568 {A M N : Type'} (x : cart A N) (x' : cart A M) (s : type24 A M) (t : type24 A N) : (term163 A M N x x' s t) = (term190 A M N x x' s t).
Proof. exact (MK_COMB (@lem8031567 A N) (@lem8031566 A M N x x' s t)). Qed.
Lemma lem8031573 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term165 A M N x s t) = (term191 A M N x s t).
Proof. exact (fun_ext (fun x' : cart A M => @lem8031568 A M N x x' s t)). Qed.
Lemma lem8031574 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8031575 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term166 A M N x s t) = (term192 A M N x s t).
Proof. exact (MK_COMB (@lem8031574 A M) (@lem8031573 A M N x s t)). Qed.
Lemma lem8031580 {A N : Type'} (x : cart A N) (t : type24 A N) : (term183 A N x t) = (term183 A N x t).
Proof. exact (eq_refl (term183 A N x t)). Qed.
Lemma lem8031581 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term170 A M N x s t) = (term193 A M N x s t).
Proof. exact (MK_COMB (@lem8031580 A N x t) (@lem8031575 A M N x s t)). Qed.
Lemma lem8031584 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term172 A M N s t) = (term194 A M N s t).
Proof. exact (fun_ext (fun x : cart A N => @lem8031581 A M N x s t)). Qed.
Lemma lem8031585 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8031586 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term173 A M N s t) = (term195 A M N s t).
Proof. exact (MK_COMB (@lem8031585 A N) (@lem8031584 A M N s t)). Qed.
Lemma lem8031591 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term195 A M N s t) = (term173 A M N s t).
Proof. exact (SYM (@lem8031586 A M N s t)). Qed.
Lemma lem8031602 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A M s) (h2 : term38 A N t) : term196 A M N t s.
Proof. exact (conj (@lem8030219 A N t h2) (@lem8030214 A M s h1)). Qed.
Lemma lem8031603 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) (h2 : term38 A M s) (h3 : term38 A N t) : term197 A M N t s.
Proof. exact (conj (@lem8030694 A M N s t h1) (@lem8031602 A M N s t h2 h3)). Qed.
Lemma lem8031613 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term198 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8031614 {A N : Type'} (s : type24 A N) (t : type24 A N) : (s = t) = (term199 A N s t).
Proof. exact (@lem8031613 (cart A N) s t). Qed.
Lemma lem8031615 {A N : Type'} (t : type24 A N) : (t = (@EMPTY (cart A N))) = (term200 A N t).
Proof. exact (@lem8031614 A N t (@EMPTY (cart A N))). Qed.
Lemma lem8031624 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8031625 {A N : Type'} (t : type24 A N) : (term38 A N t) = (term201 A N t).
Proof. exact (MK_COMB (@lem8031624) (@lem8031615 A N t)). Qed.
Lemma lem8031626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8031627 {A N : Type'} (t : type24 A N) : (term202 A N t) = (term203 A N t).
Proof. exact (MK_COMB (@lem8031626) (@lem8031625 A N t)). Qed.
Lemma lem8031631 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term198 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8031632 {A M : Type'} (s : type24 A M) (t : type24 A M) : (s = t) = (term199 A M s t).
Proof. exact (@lem8031631 (cart A M) s t). Qed.
Lemma lem8031633 {A M : Type'} (s : type24 A M) : (s = (@EMPTY (cart A M))) = (term200 A M s).
Proof. exact (@lem8031632 A M s (@EMPTY (cart A M))). Qed.
Lemma lem8031642 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8031643 {A M : Type'} (s : type24 A M) : (term38 A M s) = (term201 A M s).
Proof. exact (MK_COMB (@lem8031642) (@lem8031633 A M s)). Qed.
Lemma lem8031644 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term196 A M N t s) = (term204 A M N t s).
Proof. exact (MK_COMB (@lem8031627 A N t) (@lem8031643 A M s)). Qed.
Lemma lem8031647 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8031648 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term197 A M N t s) = (term206 A M N t s).
Proof. exact (MK_COMB (@lem8031647 A M N s t) (@lem8031644 A M N t s)). Qed.
Lemma lem8031651 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8031652 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term207 A M N t s) = (term208 A M N t s).
Proof. exact (MK_COMB (@lem8031651) (@lem8031648 A M N t s)). Qed.
Lemma lem8031675 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term186 A M N s t) = (term186 A M N s t).
Proof. exact (eq_refl (term186 A M N s t)). Qed.
Lemma lem8031676 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term209 A M N s t) = (term210 A M N s t).
Proof. exact (MK_COMB (@lem8031652 A M N t s) (@lem8031675 A M N s t)). Qed.
Lemma lem8031679 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term210 A M N s t) = (term209 A M N s t).
Proof. exact (SYM (@lem8031676 A M N s t)). Qed.
Lemma lem8031693 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8031694 {A N : Type'} (P : type24 A N) (x : cart A N) : (@IN (cart A N) x P) = (P x).
Proof. exact (@lem8031693 (cart A N) P x). Qed.
Lemma lem8031695 {A N : Type'} (t : type24 A N) (x : cart A N) : (@IN (cart A N) x t) = (t x).
Proof. exact (@lem8031694 A N t x). Qed.
Lemma lem8031696 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8031697 {A N : Type'} (t : type24 A N) (x : cart A N) : (term211 A N x t) = (term212 A N t x).
Proof. exact (MK_COMB (@lem8031696) (@lem8031695 A N t x)). Qed.
Lemma lem8031699 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8031700 {A N : Type'} (x : cart A N) : (@IN (cart A N) x (@EMPTY (cart A N))) = False.
Proof. exact (@lem8031699 (cart A N) x). Qed.
Lemma lem8031701 {A N : Type'} (t : type24 A N) (x : cart A N) : ((@IN (cart A N) x t) = (@IN (cart A N) x (@EMPTY (cart A N)))) = ((t x) = False).
Proof. exact (MK_COMB (@lem8031697 A N t x) (@lem8031700 A N x)). Qed.
Lemma lem8031703 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8031704 {A N : Type'} (t : type24 A N) (x : cart A N) : ((t x) = False) = (term213 A N t x).
Proof. exact (@lem8031703 (t x)). Qed.
Lemma lem8031705 {A N : Type'} (t : type24 A N) (x : cart A N) : ((@IN (cart A N) x t) = (@IN (cart A N) x (@EMPTY (cart A N)))) = (term213 A N t x).
Proof. exact (TRANS (@lem8031701 A N t x) (@lem8031704 A N t x)). Qed.
Lemma lem8031706 {A N : Type'} (t : type24 A N) : (term214 A N t) = (term215 A N t).
Proof. exact (fun_ext (fun x : cart A N => @lem8031705 A N t x)). Qed.
Lemma lem8031707 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8031708 {A N : Type'} (t : type24 A N) : (term200 A N t) = (term216 A N t).
Proof. exact (MK_COMB (@lem8031707 A N) (@lem8031706 A N t)). Qed.
Lemma lem8031713 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8031714 {A N : Type'} (t : type24 A N) : (term201 A N t) = (term217 A N t).
Proof. exact (MK_COMB (@lem8031713) (@lem8031708 A N t)). Qed.
Lemma lem8031715 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8031716 {A N : Type'} (t : type24 A N) : (term203 A N t) = (term218 A N t).
Proof. exact (MK_COMB (@lem8031715) (@lem8031714 A N t)). Qed.
Lemma lem8031724 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8031725 {A M : Type'} (P : type24 A M) (x : cart A M) : (@IN (cart A M) x P) = (P x).
Proof. exact (@lem8031724 (cart A M) P x). Qed.
Lemma lem8031726 {A M : Type'} (s : type24 A M) (x : cart A M) : (@IN (cart A M) x s) = (s x).
Proof. exact (@lem8031725 A M s x). Qed.
Lemma lem8031727 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8031728 {A M : Type'} (s : type24 A M) (x : cart A M) : (term211 A M x s) = (term212 A M s x).
Proof. exact (MK_COMB (@lem8031727) (@lem8031726 A M s x)). Qed.
Lemma lem8031730 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8031731 {A M : Type'} (x : cart A M) : (@IN (cart A M) x (@EMPTY (cart A M))) = False.
Proof. exact (@lem8031730 (cart A M) x). Qed.
Lemma lem8031732 {A M : Type'} (s : type24 A M) (x : cart A M) : ((@IN (cart A M) x s) = (@IN (cart A M) x (@EMPTY (cart A M)))) = ((s x) = False).
Proof. exact (MK_COMB (@lem8031728 A M s x) (@lem8031731 A M x)). Qed.
Lemma lem8031734 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8031735 {A M : Type'} (s : type24 A M) (x : cart A M) : ((s x) = False) = (term213 A M s x).
Proof. exact (@lem8031734 (s x)). Qed.
Lemma lem8031736 {A M : Type'} (s : type24 A M) (x : cart A M) : ((@IN (cart A M) x s) = (@IN (cart A M) x (@EMPTY (cart A M)))) = (term213 A M s x).
Proof. exact (TRANS (@lem8031732 A M s x) (@lem8031735 A M s x)). Qed.
Lemma lem8031737 {A M : Type'} (s : type24 A M) : (term214 A M s) = (term215 A M s).
Proof. exact (fun_ext (fun x : cart A M => @lem8031736 A M s x)). Qed.
Lemma lem8031738 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8031739 {A M : Type'} (s : type24 A M) : (term200 A M s) = (term216 A M s).
Proof. exact (MK_COMB (@lem8031738 A M) (@lem8031737 A M s)). Qed.
Lemma lem8031744 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8031745 {A M : Type'} (s : type24 A M) : (term201 A M s) = (term217 A M s).
Proof. exact (MK_COMB (@lem8031744) (@lem8031739 A M s)). Qed.
Lemma lem8031746 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term204 A M N t s) = (term219 A M N t s).
Proof. exact (MK_COMB (@lem8031716 A N t) (@lem8031745 A M s)). Qed.
Lemma lem8031749 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8031750 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term206 A M N t s) = (term220 A M N t s).
Proof. exact (MK_COMB (@lem8031749 A M N s t) (@lem8031746 A M N t s)). Qed.
Lemma lem8031753 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8031754 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term208 A M N t s) = (term221 A M N t s).
Proof. exact (MK_COMB (@lem8031753) (@lem8031750 A M N t s)). Qed.
Lemma lem8031762 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8031763 {A M : Type'} (P : type24 A M) (x : cart A M) : (@IN (cart A M) x P) = (P x).
Proof. exact (@lem8031762 (cart A M) P x). Qed.
Lemma lem8031764 {A M : Type'} (s : type24 A M) (x : cart A M) : (@IN (cart A M) x s) = (s x).
Proof. exact (@lem8031763 A M s x). Qed.
Lemma lem8031765 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8031766 {A M : Type'} (s : type24 A M) (x : cart A M) : (term183 A M x s) = (term222 A M s x).
Proof. exact (MK_COMB (@lem8031765) (@lem8031764 A M s x)). Qed.
Lemma lem8031782 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8031783 {A M : Type'} (P : type24 A M) (x : cart A M) : (@IN (cart A M) x P) = (P x).
Proof. exact (@lem8031782 (cart A M) P x). Qed.
Lemma lem8031784 {A M : Type'} (s : type24 A M) (x' : cart A M) : (@IN (cart A M) x' s) = (s x').
Proof. exact (@lem8031783 A M s x'). Qed.
Lemma lem8031785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8031786 {A M : Type'} (s : type24 A M) (x' : cart A M) : (term223 A M x' s) = (term224 A M s x').
Proof. exact (MK_COMB (@lem8031785) (@lem8031784 A M s x')). Qed.
Lemma lem8031788 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8031789 {A N : Type'} (P : type24 A N) (x : cart A N) : (@IN (cart A N) x P) = (P x).
Proof. exact (@lem8031788 (cart A N) P x). Qed.
Lemma lem8031790 {A N : Type'} (t : type24 A N) (y : cart A N) : (@IN (cart A N) y t) = (t y).
Proof. exact (@lem8031789 A N t y). Qed.
Lemma lem8031791 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term16 A M N x' s y t) = (term225 A M N s x' t y).
Proof. exact (MK_COMB (@lem8031786 A M s x') (@lem8031790 A N t y)). Qed.
Lemma lem8031794 {A M : Type'} (x : cart A M) (x' : cart A M) : (term177 A M x x') = (term177 A M x x').
Proof. exact (eq_refl (term177 A M x x')). Qed.
Lemma lem8031795 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term178 A M N x x' s y t) = (term226 A M N x s x' t y).
Proof. exact (MK_COMB (@lem8031794 A M x x') (@lem8031791 A M N s x' t y)). Qed.
Lemma lem8031798 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term179 A M N x x' s t) = (term227 A M N x s x' t).
Proof. exact (fun_ext (fun y : cart A N => @lem8031795 A M N x s x' t y)). Qed.
Lemma lem8031799 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8031800 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term180 A M N x x' s t) = (term228 A M N x s x' t).
Proof. exact (MK_COMB (@lem8031799 A N) (@lem8031798 A M N x s x' t)). Qed.
Lemma lem8031805 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term181 A M N x s t) = (term229 A M N x s t).
Proof. exact (fun_ext (fun x' : cart A M => @lem8031800 A M N x s x' t)). Qed.
Lemma lem8031806 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8031807 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term182 A M N x s t) = (term230 A M N x s t).
Proof. exact (MK_COMB (@lem8031806 A M) (@lem8031805 A M N x s t)). Qed.
Lemma lem8031812 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term184 A M N x s t) = (term231 A M N x s t).
Proof. exact (MK_COMB (@lem8031766 A M s x) (@lem8031807 A M N x s t)). Qed.
Lemma lem8031815 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term185 A M N s t) = (term232 A M N s t).
Proof. exact (fun_ext (fun x : cart A M => @lem8031812 A M N x s t)). Qed.
Lemma lem8031816 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8031817 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term186 A M N s t) = (term233 A M N s t).
Proof. exact (MK_COMB (@lem8031816 A M) (@lem8031815 A M N s t)). Qed.
Lemma lem8031822 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term210 A M N s t) = (term234 A M N s t).
Proof. exact (MK_COMB (@lem8031754 A M N t s) (@lem8031817 A M N s t)). Qed.
Lemma lem8031825 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term234 A M N s t) = (term210 A M N s t).
Proof. exact (SYM (@lem8031822 A M N s t)). Qed.
Lemma lem8031827 (p : Prop) : p = (term235 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8031828 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term234 A M N s t) = (term236 A M N s t).
Proof. exact (@lem8031827 (term234 A M N s t)). Qed.
Lemma lem8031829 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term236 A M N s t) = (term234 A M N s t).
Proof. exact (SYM (@lem8031828 A M N s t)). Qed.
Lemma lem8031830 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term237 A M N s t) : term237 A M N s t.
Proof. exact (h1). Qed.
Lemma lem8031833 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term236 A M N s t) : term236 A M N s t.
Proof. exact (h1). Qed.
Lemma lem8031834 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term238 A M N s t.
Proof. exact (fun h0 : term236 A M N s t => @lem8031833 A M N s t h0). Qed.
Lemma lem8031835 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term238 A M N s t) : term238 A M N s t.
Proof. exact (h1). Qed.
Lemma lem8031836 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term236 A M N s t) : term236 A M N s t.
Proof. exact (h1). Qed.
Lemma lem8031837 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term236 A M N s t) (h2 : term238 A M N s t) : term236 A M N s t.
Proof. exact (@lem8031835 A M N s t h2 (@lem8031836 A M N s t h1)). Qed.
Lemma lem8031838 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term236 A M N s t) : term239 A M N s t.
Proof. exact (fun h0 : term238 A M N s t => @lem8031837 A M N s t h1 h0). Qed.
Lemma lem8031839 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term238 A M N s t) : term238 A M N s t.
Proof. exact (h1). Qed.
Lemma lem8031840 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term236 A M N s t) (h2 : term238 A M N s t) : term236 A M N s t.
Proof. exact (@lem8031838 A M N s t h1 (@lem8031839 A M N s t h2)). Qed.
Lemma lem8031841 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term238 A M N s t) : term238 A M N s t.
Proof. exact (fun h0 : term236 A M N s t => @lem8031840 A M N s t h0 h1). Qed.
Lemma lem8031842 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term240 A M N s t.
Proof. exact (fun h0 : term238 A M N s t => @lem8031841 A M N s t h0). Qed.
Lemma lem8031845 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term238 A M N s t.
Proof. exact (@lem8031842 A M N s t (@lem8031834 A M N s t)). Qed.
Lemma lem8031846 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term238 A M N s t.
Proof. exact (@lem8031845 A M N s t). Qed.
Lemma lem8031856 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8031857 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term236 A M N s t) = (term241 A M N s t).
Proof. exact (@lem8031856 (term237 A M N s t)). Qed.
Lemma lem8031859 (t : Prop) : (term242 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8031860 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term241 A M N s t) = (term234 A M N s t).
Proof. exact (@lem8031859 (term234 A M N s t)). Qed.
Lemma lem8031863 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term236 A M N s t) = (term234 A M N s t).
Proof. exact (TRANS (@lem8031857 A M N s t) (@lem8031860 A M N s t)). Qed.
Lemma lem8031887 {A : Type'} (P : Prop) (Q : A -> Prop) : (term243 A P Q) = (term244 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem8031888 {A N : Type'} (P : Prop) (Q : type24 A N) : (term245 A N P Q) = (term246 A N P Q).
Proof. exact (@lem8031887 (cart A N) P Q). Qed.
Lemma lem8031889 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term247 A M N x s x' t) = (term248 A M N x s x' t).
Proof. exact (@lem8031888 A N (x = x') (term249 A M N s x' t)). Qed.
Lemma lem8031890 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term250 A M N s x' t y) = (term225 A M N s x' t y).
Proof. exact (eq_refl (term250 A M N s x' t y)). Qed.
Lemma lem8031891 {A M : Type'} (x : cart A M) (x' : cart A M) : (term177 A M x x') = (term177 A M x x').
Proof. exact (eq_refl (term177 A M x x')). Qed.
Lemma lem8031892 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term251 A M N x s x' t y) = (term226 A M N x s x' t y).
Proof. exact (MK_COMB (@lem8031891 A M x x') (@lem8031890 A M N s x' t y)). Qed.
Lemma lem8031893 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term252 A M N x s x' t) = (term227 A M N x s x' t).
Proof. exact (fun_ext (fun y : cart A N => @lem8031892 A M N x s x' t y)). Qed.
Lemma lem8031894 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8031895 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term247 A M N x s x' t) = (term228 A M N x s x' t).
Proof. exact (MK_COMB (@lem8031894 A N) (@lem8031893 A M N x s x' t)). Qed.
Lemma lem8031896 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8031897 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term253 A M N x s x' t) = (term254 A M N x s x' t).
Proof. exact (MK_COMB (@lem8031896) (@lem8031895 A M N x s x' t)). Qed.
Lemma lem8031898 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term250 A M N s x' t y) = (term225 A M N s x' t y).
Proof. exact (eq_refl (term250 A M N s x' t y)). Qed.
Lemma lem8031899 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term255 A M N s x' t) = (term249 A M N s x' t).
Proof. exact (fun_ext (fun y : cart A N => @lem8031898 A M N s x' t y)). Qed.
Lemma lem8031900 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8031901 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term256 A M N s x' t) = (term257 A M N s x' t).
Proof. exact (MK_COMB (@lem8031900 A N) (@lem8031899 A M N s x' t)). Qed.
Lemma lem8031902 {A M : Type'} (x : cart A M) (x' : cart A M) : (term177 A M x x') = (term177 A M x x').
Proof. exact (eq_refl (term177 A M x x')). Qed.
Lemma lem8031903 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term248 A M N x s x' t) = (term258 A M N x s x' t).
Proof. exact (MK_COMB (@lem8031902 A M x x') (@lem8031901 A M N s x' t)). Qed.
Lemma lem8031904 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : ((term247 A M N x s x' t) = (term248 A M N x s x' t)) = ((term228 A M N x s x' t) = (term258 A M N x s x' t)).
Proof. exact (MK_COMB (@lem8031897 A M N x s x' t) (@lem8031903 A M N x s x' t)). Qed.
Lemma lem8031905 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term228 A M N x s x' t) = (term258 A M N x s x' t).
Proof. exact (EQ_MP (@lem8031904 A M N x s x' t) (@lem8031889 A M N x s x' t)). Qed.
Lemma lem8031909 {A : Type'} (P : Prop) (Q : A -> Prop) : (term243 A P Q) = (term244 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem8031910 {A N : Type'} (P : Prop) (Q : type24 A N) : (term245 A N P Q) = (term246 A N P Q).
Proof. exact (@lem8031909 (cart A N) P Q). Qed.
Lemma lem8031911 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term257 A M N s x' t) = (term259 A M N s x' t).
Proof. exact (@lem8031910 A N (s x') t). Qed.
Lemma lem8031918 {A M : Type'} (x : cart A M) (x' : cart A M) : (term177 A M x x') = (term177 A M x x').
Proof. exact (eq_refl (term177 A M x x')). Qed.
Lemma lem8031919 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term258 A M N x s x' t) = (term260 A M N x s x' t).
Proof. exact (MK_COMB (@lem8031918 A M x x') (@lem8031911 A M N s x' t)). Qed.
Lemma lem8031922 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term228 A M N x s x' t) = (term260 A M N x s x' t).
Proof. exact (TRANS (@lem8031905 A M N x s x' t) (@lem8031919 A M N x s x' t)). Qed.
Lemma lem8031923 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term229 A M N x s t) = (term261 A M N x s t).
Proof. exact (fun_ext (fun x' : cart A M => @lem8031922 A M N x s x' t)). Qed.
Lemma lem8031924 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8031925 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term230 A M N x s t) = (term262 A M N x s t).
Proof. exact (MK_COMB (@lem8031924 A M) (@lem8031923 A M N x s t)). Qed.
Lemma lem8031974 {A M : Type'} (s : type24 A M) (x : cart A M) : (term222 A M s x) = (term222 A M s x).
Proof. exact (eq_refl (term222 A M s x)). Qed.
Lemma lem8031975 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term231 A M N x s t) = (term263 A M N x s t).
Proof. exact (MK_COMB (@lem8031974 A M s x) (@lem8031925 A M N x s t)). Qed.
Lemma lem8031978 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term232 A M N s t) = (term264 A M N s t).
Proof. exact (fun_ext (fun x : cart A M => @lem8031975 A M N x s t)). Qed.
Lemma lem8031979 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8031980 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term233 A M N s t) = (term265 A M N s t).
Proof. exact (MK_COMB (@lem8031979 A M) (@lem8031978 A M N s t)). Qed.
Lemma lem8031985 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term221 A M N t s) = (term221 A M N t s).
Proof. exact (eq_refl (term221 A M N t s)). Qed.
Lemma lem8031986 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term234 A M N s t) = (term266 A M N s t).
Proof. exact (MK_COMB (@lem8031985 A M N t s) (@lem8031980 A M N s t)). Qed.
Lemma lem8031989 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term236 A M N s t) = (term266 A M N s t).
Proof. exact (TRANS (@lem8031863 A M N s t) (@lem8031986 A M N s t)). Qed.
Lemma lem8031990 {A M N : Type'} (t : type24 A N) : (term267 A M N t) = (term268 A M N t).
Proof. exact (fun_ext (fun s : type24 A M => @lem8031989 A M N s t)). Qed.
Lemma lem8031991 {A M : Type'} : (@all ((cart A M) -> Prop)) = (@all ((cart A M) -> Prop)).
Proof. exact (eq_refl (@all ((cart A M) -> Prop))). Qed.
Lemma lem8031992 {A M N : Type'} (t : type24 A N) : (term269 A M N t) = (term270 A M N t).
Proof. exact (MK_COMB (@lem8031991 A M) (@lem8031990 A M N t)). Qed.
Lemma lem8031997 {A M N : Type'} : (term271 A M N) = (term272 A M N).
Proof. exact (fun_ext (fun t : type24 A N => @lem8031992 A M N t)). Qed.
Lemma lem8031998 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem8032007 {A M N : Type'} : (term273 A M N) = (term274 A M N).
Proof. exact (MK_COMB (@lem8031998 A N) (@lem8031997 A M N)). Qed.
Lemma lem8032008 {A N : Type'} (t : type24 A N) (y : cart A N) : (t y) = (t y).
Proof. exact (eq_refl (t y)). Qed.
Lemma lem8032009 {A N : Type'} (t : type24 A N) : (term275 A N t) = (term275 A N t).
Proof. exact (fun_ext (fun y : cart A N => @lem8032008 A N t y)). Qed.
Lemma lem8032010 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8032011 {A N : Type'} (t : type24 A N) : (term276 A N t) = (term276 A N t).
Proof. exact (MK_COMB (@lem8032010 A N) (@lem8032009 A N t)). Qed.
Lemma lem8032014 {A M : Type'} (s : type24 A M) (x' : cart A M) : (term224 A M s x') = (term224 A M s x').
Proof. exact (eq_refl (term224 A M s x')). Qed.
Lemma lem8032015 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term259 A M N s x' t) = (term259 A M N s x' t).
Proof. exact (MK_COMB (@lem8032014 A M s x') (@lem8032011 A N t)). Qed.
Lemma lem8032018 {A M : Type'} (x : cart A M) (x' : cart A M) : (term177 A M x x') = (term177 A M x x').
Proof. exact (eq_refl (term177 A M x x')). Qed.
Lemma lem8032019 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term260 A M N x s x' t) = (term260 A M N x s x' t).
Proof. exact (MK_COMB (@lem8032018 A M x x') (@lem8032015 A M N s x' t)). Qed.
Lemma lem8032020 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term261 A M N x s t) = (term261 A M N x s t).
Proof. exact (fun_ext (fun x' : cart A M => @lem8032019 A M N x s x' t)). Qed.
Lemma lem8032021 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8032022 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term262 A M N x s t) = (term262 A M N x s t).
Proof. exact (MK_COMB (@lem8032021 A M) (@lem8032020 A M N x s t)). Qed.
Lemma lem8032025 {A M : Type'} (s : type24 A M) (x : cart A M) : (term222 A M s x) = (term222 A M s x).
Proof. exact (eq_refl (term222 A M s x)). Qed.
Lemma lem8032026 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term263 A M N x s t) = (term263 A M N x s t).
Proof. exact (MK_COMB (@lem8032025 A M s x) (@lem8032022 A M N x s t)). Qed.
Lemma lem8032027 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term264 A M N s t) = (term264 A M N s t).
Proof. exact (fun_ext (fun x : cart A M => @lem8032026 A M N x s t)). Qed.
Lemma lem8032028 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8032029 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term265 A M N s t) = (term265 A M N s t).
Proof. exact (MK_COMB (@lem8032028 A M) (@lem8032027 A M N s t)). Qed.
Lemma lem8032032 {A M : Type'} (s : type24 A M) (x : cart A M) : (term213 A M s x) = (term213 A M s x).
Proof. exact (eq_refl (term213 A M s x)). Qed.
Lemma lem8032033 {A M : Type'} (s : type24 A M) : (term215 A M s) = (term215 A M s).
Proof. exact (fun_ext (fun x : cart A M => @lem8032032 A M s x)). Qed.
Lemma lem8032034 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8032035 {A M : Type'} (s : type24 A M) : (term216 A M s) = (term216 A M s).
Proof. exact (MK_COMB (@lem8032034 A M) (@lem8032033 A M s)). Qed.
Lemma lem8032036 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8032037 {A M : Type'} (s : type24 A M) : (term217 A M s) = (term217 A M s).
Proof. exact (MK_COMB (@lem8032036) (@lem8032035 A M s)). Qed.
Lemma lem8032040 {A N : Type'} (t : type24 A N) (x : cart A N) : (term213 A N t x) = (term213 A N t x).
Proof. exact (eq_refl (term213 A N t x)). Qed.
Lemma lem8032041 {A N : Type'} (t : type24 A N) : (term215 A N t) = (term215 A N t).
Proof. exact (fun_ext (fun x : cart A N => @lem8032040 A N t x)). Qed.
Lemma lem8032042 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8032043 {A N : Type'} (t : type24 A N) : (term216 A N t) = (term216 A N t).
Proof. exact (MK_COMB (@lem8032042 A N) (@lem8032041 A N t)). Qed.
Lemma lem8032044 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8032045 {A N : Type'} (t : type24 A N) : (term217 A N t) = (term217 A N t).
Proof. exact (MK_COMB (@lem8032044) (@lem8032043 A N t)). Qed.
Lemma lem8032046 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8032047 {A N : Type'} (t : type24 A N) : (term218 A N t) = (term218 A N t).
Proof. exact (MK_COMB (@lem8032046) (@lem8032045 A N t)). Qed.
Lemma lem8032048 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term219 A M N t s) = (term219 A M N t s).
Proof. exact (MK_COMB (@lem8032047 A N t) (@lem8032037 A M s)). Qed.
Lemma lem8032051 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8032052 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term220 A M N t s) = (term220 A M N t s).
Proof. exact (MK_COMB (@lem8032051 A M N s t) (@lem8032048 A M N t s)). Qed.
Lemma lem8032053 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8032054 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term221 A M N t s) = (term221 A M N t s).
Proof. exact (MK_COMB (@lem8032053) (@lem8032052 A M N t s)). Qed.
Lemma lem8032055 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term266 A M N s t) = (term266 A M N s t).
Proof. exact (MK_COMB (@lem8032054 A M N t s) (@lem8032029 A M N s t)). Qed.
Lemma lem8032056 {A M N : Type'} (t : type24 A N) : (term268 A M N t) = (term268 A M N t).
Proof. exact (fun_ext (fun s : type24 A M => @lem8032055 A M N s t)). Qed.
Lemma lem8032057 {A M : Type'} : (@all ((cart A M) -> Prop)) = (@all ((cart A M) -> Prop)).
Proof. exact (eq_refl (@all ((cart A M) -> Prop))). Qed.
Lemma lem8032058 {A M N : Type'} (t : type24 A N) : (term270 A M N t) = (term270 A M N t).
Proof. exact (MK_COMB (@lem8032057 A M) (@lem8032056 A M N t)). Qed.
Lemma lem8032059 {A M N : Type'} : (term272 A M N) = (term272 A M N).
Proof. exact (fun_ext (fun t : type24 A N => @lem8032058 A M N t)). Qed.
Lemma lem8032060 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem8032061 {A M N : Type'} : (term274 A M N) = (term274 A M N).
Proof. exact (MK_COMB (@lem8032060 A N) (@lem8032059 A M N)). Qed.
Lemma lem8032118 {A M N : Type'} : (term273 A M N) = (term274 A M N).
Proof. exact (TRANS (@lem8032007 A M N) (@lem8032061 A M N)). Qed.
Lemma lem8032119 {A M N : Type'} : (term274 A M N) = (term273 A M N).
Proof. exact (SYM (@lem8032118 A M N)). Qed.
Lemma lem8032120 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : term220 A M N t s) : term220 A M N t s.
Proof. exact (h1). Qed.
Lemma lem8032123 (p : Prop) : p = (term235 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8032124 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term262 A M N x s t) = (term277 A M N x s t).
Proof. exact (@lem8032123 (term262 A M N x s t)). Qed.
Lemma lem8032125 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term277 A M N x s t) = (term262 A M N x s t).
Proof. exact (SYM (@lem8032124 A M N x s t)). Qed.
Lemma lem8032126 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) (h1 : term278 A M N x s t) : term278 A M N x s t.
Proof. exact (h1). Qed.
Lemma lem8032130 {A N : Type'} (t : type24 A N) (x : cart A N) : (term279 A N t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem8032131 {A N : Type'} (P : type24 A N) : (term280 A N P) = (term281 A N P).
Proof. exact (@lem18392 (cart A N) P). Qed.
Lemma lem8032132 {A N : Type'} (t : type24 A N) : (term217 A N t) = (term282 A N t).
Proof. exact (@lem8032131 A N (term215 A N t)). Qed.
Lemma lem8032133 {A N : Type'} (t : type24 A N) (x : cart A N) : (term283 A N t x) = (term213 A N t x).
Proof. exact (eq_refl (term283 A N t x)). Qed.
Lemma lem8032134 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8032135 {A N : Type'} (t : type24 A N) (x : cart A N) : (term284 A N t x) = (term279 A N t x).
Proof. exact (MK_COMB (@lem8032134) (@lem8032133 A N t x)). Qed.
Lemma lem8032136 {A N : Type'} (t : type24 A N) (x : cart A N) : (term284 A N t x) = (t x).
Proof. exact (TRANS (@lem8032135 A N t x) (@lem8032130 A N t x)). Qed.
Lemma lem8032137 {A N : Type'} (t : type24 A N) : (term285 A N t) = (term275 A N t).
Proof. exact (fun_ext (fun x : cart A N => @lem8032136 A N t x)). Qed.
Lemma lem8032138 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8032139 {A N : Type'} (t : type24 A N) : (term282 A N t) = (term276 A N t).
Proof. exact (MK_COMB (@lem8032138 A N) (@lem8032137 A N t)). Qed.
Lemma lem8032140 {A N : Type'} (t : type24 A N) : (term217 A N t) = (term276 A N t).
Proof. exact (TRANS (@lem8032132 A N t) (@lem8032139 A N t)). Qed.
Lemma lem8032143 {A M : Type'} (s : type24 A M) (x : cart A M) : (term279 A M s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem8032144 {A M : Type'} (P : type24 A M) : (term280 A M P) = (term281 A M P).
Proof. exact (@lem18392 (cart A M) P). Qed.
Lemma lem8032145 {A M : Type'} (s : type24 A M) : (term217 A M s) = (term282 A M s).
Proof. exact (@lem8032144 A M (term215 A M s)). Qed.
Lemma lem8032146 {A M : Type'} (s : type24 A M) (x : cart A M) : (term283 A M s x) = (term213 A M s x).
Proof. exact (eq_refl (term283 A M s x)). Qed.
Lemma lem8032147 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8032148 {A M : Type'} (s : type24 A M) (x : cart A M) : (term284 A M s x) = (term279 A M s x).
Proof. exact (MK_COMB (@lem8032147) (@lem8032146 A M s x)). Qed.
Lemma lem8032149 {A M : Type'} (s : type24 A M) (x : cart A M) : (term284 A M s x) = (s x).
Proof. exact (TRANS (@lem8032148 A M s x) (@lem8032143 A M s x)). Qed.
Lemma lem8032150 {A M : Type'} (s : type24 A M) : (term285 A M s) = (term275 A M s).
Proof. exact (fun_ext (fun x : cart A M => @lem8032149 A M s x)). Qed.
Lemma lem8032151 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8032152 {A M : Type'} (s : type24 A M) : (term282 A M s) = (term276 A M s).
Proof. exact (MK_COMB (@lem8032151 A M) (@lem8032150 A M s)). Qed.
Lemma lem8032153 {A M : Type'} (s : type24 A M) : (term217 A M s) = (term276 A M s).
Proof. exact (TRANS (@lem8032145 A M s) (@lem8032152 A M s)). Qed.
Lemma lem8032154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8032155 {A N : Type'} (t : type24 A N) : (term218 A N t) = (term286 A N t).
Proof. exact (MK_COMB (@lem8032154) (@lem8032140 A N t)). Qed.
Lemma lem8032156 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term219 A M N t s) = (term287 A M N t s).
Proof. exact (MK_COMB (@lem8032155 A N t) (@lem8032153 A M s)). Qed.
Lemma lem8032158 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8032159 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term220 A M N t s) = (term288 A M N t s).
Proof. exact (MK_COMB (@lem8032158 A M N s t) (@lem8032156 A M N t s)). Qed.
Lemma lem8032170 {A : Type'} (P : A -> Prop) (Q : Prop) : (term289 A P Q) = (term290 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8032171 {A N : Type'} (P : type24 A N) (Q : Prop) : (term291 A N P Q) = (term292 A N P Q).
Proof. exact (@lem8032170 (cart A N) P Q). Qed.
Lemma lem8032172 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term287 A M N t s) = (term293 A M N t s).
Proof. exact (@lem8032171 A N t (term276 A M s)). Qed.
Lemma lem8032174 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8032175 {A M : Type'} (P : Prop) (Q : type24 A M) : (term246 A M P Q) = (term245 A M P Q).
Proof. exact (@lem8032174 (cart A M) P Q). Qed.
Lemma lem8032176 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term294 A M N t x s) = (term295 A M N t x s).
Proof. exact (@lem8032175 A M (t x) s). Qed.
Lemma lem8032177 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term296 A M N t s) = (term297 A M N t s).
Proof. exact (fun_ext (fun x : cart A N => @lem8032176 A M N t x s)). Qed.
Lemma lem8032178 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8032179 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term293 A M N t s) = (term298 A M N t s).
Proof. exact (MK_COMB (@lem8032178 A N) (@lem8032177 A M N t s)). Qed.
Lemma lem8032180 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term287 A M N t s) = (term298 A M N t s).
Proof. exact (TRANS (@lem8032172 A M N t s) (@lem8032179 A M N t s)). Qed.
Lemma lem8032181 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8032182 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term288 A M N t s) = (term299 A M N t s).
Proof. exact (MK_COMB (@lem8032181 A M N s t) (@lem8032180 A M N t s)). Qed.
Lemma lem8032184 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8032185 {A N : Type'} (P : Prop) (Q : type24 A N) : (term246 A N P Q) = (term245 A N P Q).
Proof. exact (@lem8032184 (cart A N) P Q). Qed.
Lemma lem8032186 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term300 A M N t s) = (term301 A M N t s).
Proof. exact (@lem8032185 A N (term35 A M N s t) (term297 A M N t s)). Qed.
Lemma lem8032187 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term302 A M N t s x) = (term295 A M N t x s).
Proof. exact (eq_refl (term302 A M N t s x)). Qed.
Lemma lem8032188 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term303 A M N t s) = (term297 A M N t s).
Proof. exact (fun_ext (fun x : cart A N => @lem8032187 A M N t x s)). Qed.
Lemma lem8032189 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8032190 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term304 A M N t s) = (term298 A M N t s).
Proof. exact (MK_COMB (@lem8032189 A N) (@lem8032188 A M N t s)). Qed.
Lemma lem8032191 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8032192 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term300 A M N t s) = (term299 A M N t s).
Proof. exact (MK_COMB (@lem8032191 A M N s t) (@lem8032190 A M N t s)). Qed.
Lemma lem8032193 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8032194 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term305 A M N t s) = (term306 A M N t s).
Proof. exact (MK_COMB (@lem8032193) (@lem8032192 A M N t s)). Qed.
Lemma lem8032195 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term302 A M N t s x) = (term295 A M N t x s).
Proof. exact (eq_refl (term302 A M N t s x)). Qed.
Lemma lem8032196 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8032197 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term307 A M N t s x) = (term308 A M N t x s).
Proof. exact (MK_COMB (@lem8032196 A M N s t) (@lem8032195 A M N t x s)). Qed.
Lemma lem8032198 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term309 A M N t s) = (term310 A M N t s).
Proof. exact (fun_ext (fun x : cart A N => @lem8032197 A M N t x s)). Qed.
Lemma lem8032199 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8032200 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term301 A M N t s) = (term311 A M N t s).
Proof. exact (MK_COMB (@lem8032199 A N) (@lem8032198 A M N t s)). Qed.
Lemma lem8032201 {A M N : Type'} (t : type24 A N) (s : type24 A M) : ((term300 A M N t s) = (term301 A M N t s)) = ((term299 A M N t s) = (term311 A M N t s)).
Proof. exact (MK_COMB (@lem8032194 A M N t s) (@lem8032200 A M N t s)). Qed.
Lemma lem8032202 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term299 A M N t s) = (term311 A M N t s).
Proof. exact (EQ_MP (@lem8032201 A M N t s) (@lem8032186 A M N t s)). Qed.
Lemma lem8032204 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8032205 {A M : Type'} (P : Prop) (Q : type24 A M) : (term246 A M P Q) = (term245 A M P Q).
Proof. exact (@lem8032204 (cart A M) P Q). Qed.
Lemma lem8032206 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term312 A M N t x s) = (term313 A M N t x s).
Proof. exact (@lem8032205 A M (term35 A M N s t) (term314 A M N t x s)). Qed.
Lemma lem8032207 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) (x' : cart A M) : (term315 A M N t x s x') = (term316 A M N t x s x').
Proof. exact (eq_refl (term315 A M N t x s x')). Qed.
Lemma lem8032208 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term317 A M N t x s) = (term314 A M N t x s).
Proof. exact (fun_ext (fun x' : cart A M => @lem8032207 A M N t x s x')). Qed.
Lemma lem8032209 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8032210 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term318 A M N t x s) = (term295 A M N t x s).
Proof. exact (MK_COMB (@lem8032209 A M) (@lem8032208 A M N t x s)). Qed.
Lemma lem8032211 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8032212 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term312 A M N t x s) = (term308 A M N t x s).
Proof. exact (MK_COMB (@lem8032211 A M N s t) (@lem8032210 A M N t x s)). Qed.
Lemma lem8032213 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8032214 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term319 A M N t x s) = (term320 A M N t x s).
Proof. exact (MK_COMB (@lem8032213) (@lem8032212 A M N t x s)). Qed.
Lemma lem8032215 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) (x' : cart A M) : (term315 A M N t x s x') = (term316 A M N t x s x').
Proof. exact (eq_refl (term315 A M N t x s x')). Qed.
Lemma lem8032216 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8032217 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) (x' : cart A M) : (term321 A M N t x s x') = (term322 A M N t x s x').
Proof. exact (MK_COMB (@lem8032216 A M N s t) (@lem8032215 A M N t x s x')). Qed.
Lemma lem8032218 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term323 A M N t x s) = (term324 A M N t x s).
Proof. exact (fun_ext (fun x' : cart A M => @lem8032217 A M N t x s x')). Qed.
Lemma lem8032219 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8032220 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term313 A M N t x s) = (term325 A M N t x s).
Proof. exact (MK_COMB (@lem8032219 A M) (@lem8032218 A M N t x s)). Qed.
Lemma lem8032221 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : ((term312 A M N t x s) = (term313 A M N t x s)) = ((term308 A M N t x s) = (term325 A M N t x s)).
Proof. exact (MK_COMB (@lem8032214 A M N t x s) (@lem8032220 A M N t x s)). Qed.
Lemma lem8032222 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term308 A M N t x s) = (term325 A M N t x s).
Proof. exact (EQ_MP (@lem8032221 A M N t x s) (@lem8032206 A M N t x s)). Qed.
Lemma lem8032223 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term310 A M N t s) = (term326 A M N t s).
Proof. exact (fun_ext (fun x : cart A N => @lem8032222 A M N t x s)). Qed.
Lemma lem8032224 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8032225 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term311 A M N t s) = (term327 A M N t s).
Proof. exact (MK_COMB (@lem8032224 A N) (@lem8032223 A M N t s)). Qed.
Lemma lem8032226 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term299 A M N t s) = (term327 A M N t s).
Proof. exact (TRANS (@lem8032202 A M N t s) (@lem8032225 A M N t s)). Qed.
Lemma lem8032228 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term288 A M N t s) = (term327 A M N t s).
Proof. exact (TRANS (@lem8032182 A M N t s) (@lem8032226 A M N t s)). Qed.
Lemma lem8032229 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term220 A M N t s) = (term327 A M N t s).
Proof. exact (TRANS (@lem8032159 A M N t s) (@lem8032228 A M N t s)). Qed.
Lemma lem8032230 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : term220 A M N t s) : term327 A M N t s.
Proof. exact (EQ_MP (@lem8032229 A M N t s) (@lem8032120 A M N t s h1)). Qed.
Lemma lem8032236 {A M : Type'} (s : type24 A M) (x : cart A M) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem8032240 {A N : Type'} (P : type24 A N) : (term328 A N P) = (term216 A N P).
Proof. exact (@lem18394 (cart A N) P). Qed.
Lemma lem8032241 {A N : Type'} (t : type24 A N) : (term329 A N t) = (term330 A N t).
Proof. exact (@lem8032240 A N (term275 A N t)). Qed.
Lemma lem8032242 {A N : Type'} (t : type24 A N) (y : cart A N) : (term331 A N t y) = (t y).
Proof. exact (eq_refl (term331 A N t y)). Qed.
Lemma lem8032243 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8032245 {A N : Type'} (t : type24 A N) (y : cart A N) : (term332 A N t y) = (term213 A N t y).
Proof. exact (MK_COMB (@lem8032243) (@lem8032242 A N t y)). Qed.
Lemma lem8032246 {A N : Type'} (t : type24 A N) : (term333 A N t) = (term215 A N t).
Proof. exact (fun_ext (fun y : cart A N => @lem8032245 A N t y)). Qed.
Lemma lem8032247 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8032248 {A N : Type'} (t : type24 A N) : (term330 A N t) = (term216 A N t).
Proof. exact (MK_COMB (@lem8032247 A N) (@lem8032246 A N t)). Qed.
Lemma lem8032249 {A N : Type'} (t : type24 A N) : (term329 A N t) = (term216 A N t).
Proof. exact (TRANS (@lem8032241 A N t) (@lem8032248 A N t)). Qed.
Lemma lem8032251 {A M : Type'} (s : type24 A M) (x' : cart A M) : (term334 A M s x') = (term334 A M s x').
Proof. exact (eq_refl (term334 A M s x')). Qed.
Lemma lem8032252 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term335 A M N s x' t) = (term336 A M N s x' t).
Proof. exact (MK_COMB (@lem8032251 A M s x') (@lem8032249 A N t)). Qed.
Lemma lem8032253 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term337 A M N s x' t) = (term335 A M N s x' t).
Proof. exact (@lem17045 (s x') (term276 A N t)). Qed.
Lemma lem8032254 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term337 A M N s x' t) = (term336 A M N s x' t).
Proof. exact (TRANS (@lem8032253 A M N s x' t) (@lem8032252 A M N s x' t)). Qed.
Lemma lem8032256 {A M : Type'} (x : cart A M) (x' : cart A M) : (term338 A M x x') = (term338 A M x x').
Proof. exact (eq_refl (term338 A M x x')). Qed.
Lemma lem8032257 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term339 A M N x s x' t) = (term340 A M N x s x' t).
Proof. exact (MK_COMB (@lem8032256 A M x x') (@lem8032254 A M N s x' t)). Qed.
Lemma lem8032258 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term341 A M N x s x' t) = (term339 A M N x s x' t).
Proof. exact (@lem17045 (x = x') (term259 A M N s x' t)). Qed.
Lemma lem8032259 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term341 A M N x s x' t) = (term340 A M N x s x' t).
Proof. exact (TRANS (@lem8032258 A M N x s x' t) (@lem8032257 A M N x s x' t)). Qed.
Lemma lem8032260 {A M : Type'} (P : type24 A M) : (term328 A M P) = (term216 A M P).
Proof. exact (@lem18394 (cart A M) P). Qed.
Lemma lem8032261 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term278 A M N x s t) = (term342 A M N x s t).
Proof. exact (@lem8032260 A M (term261 A M N x s t)). Qed.
Lemma lem8032262 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term343 A M N x s t x') = (term260 A M N x s x' t).
Proof. exact (eq_refl (term343 A M N x s t x')). Qed.
Lemma lem8032263 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8032264 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term344 A M N x s t x') = (term341 A M N x s x' t).
Proof. exact (MK_COMB (@lem8032263) (@lem8032262 A M N x s x' t)). Qed.
Lemma lem8032265 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term344 A M N x s t x') = (term340 A M N x s x' t).
Proof. exact (TRANS (@lem8032264 A M N x s x' t) (@lem8032259 A M N x s x' t)). Qed.
Lemma lem8032266 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term345 A M N x s t) = (term346 A M N x s t).
Proof. exact (fun_ext (fun x' : cart A M => @lem8032265 A M N x s x' t)). Qed.
Lemma lem8032267 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8032268 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term342 A M N x s t) = (term347 A M N x s t).
Proof. exact (MK_COMB (@lem8032267 A M) (@lem8032266 A M N x s t)). Qed.
Lemma lem8032325 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term278 A M N x s t) = (term347 A M N x s t).
Proof. exact (TRANS (@lem8032261 A M N x s t) (@lem8032268 A M N x s t)). Qed.
Lemma lem8032326 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) (h1 : term278 A M N x s t) : term347 A M N x s t.
Proof. exact (EQ_MP (@lem8032325 A M N x s t) (@lem8032126 A M N x s t h1)). Qed.
Lemma lem8032327 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (h1 : term325 A M N t x' s) : term325 A M N t x' s.
Proof. exact (h1). Qed.
Lemma lem8032328 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term322 A M N t x' s x'') : term322 A M N t x' s x''.
Proof. exact (h1). Qed.
Lemma lem8032333 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8032334 {A M : Type'} (f : type24 A M) (x : cart A M) : (f x) = (@I ((cart A M) -> Prop) f x).
Proof. exact (@lem8032333 (cart A M) Prop f x). Qed.
Lemma lem8032336 {A M : Type'} (s : type24 A M) (x : cart A M) : (s x) = (@I ((cart A M) -> Prop) s x).
Proof. exact (@lem8032334 A M s x). Qed.
Lemma lem8032338 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8032343 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8032344 {A N : Type'} (f : type24 A N) (x : cart A N) : (f x) = (@I ((cart A N) -> Prop) f x).
Proof. exact (@lem8032343 (cart A N) Prop f x). Qed.
Lemma lem8032346 {A N : Type'} (t : type24 A N) (y : cart A N) : (t y) = (@I ((cart A N) -> Prop) t y).
Proof. exact (@lem8032344 A N t y). Qed.
Lemma lem8032347 {A N : Type'} (t : type24 A N) (y : cart A N) : (term213 A N t y) = (term348 A N t y).
Proof. exact (MK_COMB (@lem8032338) (@lem8032346 A N t y)). Qed.
Lemma lem8032348 {A N : Type'} (t : type24 A N) : (term215 A N t) = (term349 A N t).
Proof. exact (fun_ext (fun y : cart A N => @lem8032347 A N t y)). Qed.
Lemma lem8032349 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8032350 {A N : Type'} (t : type24 A N) : (term216 A N t) = (term350 A N t).
Proof. exact (MK_COMB (@lem8032349 A N) (@lem8032348 A N t)). Qed.
Lemma lem8032351 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8032356 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8032357 {A M : Type'} (f : type24 A M) (x : cart A M) : (f x) = (@I ((cart A M) -> Prop) f x).
Proof. exact (@lem8032356 (cart A M) Prop f x). Qed.
Lemma lem8032359 {A M : Type'} (s : type24 A M) (x' : cart A M) : (s x') = (@I ((cart A M) -> Prop) s x').
Proof. exact (@lem8032357 A M s x'). Qed.
Lemma lem8032360 {A M : Type'} (s : type24 A M) (x' : cart A M) : (term213 A M s x') = (term348 A M s x').
Proof. exact (MK_COMB (@lem8032351) (@lem8032359 A M s x')). Qed.
Lemma lem8032361 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8032362 {A M : Type'} (s : type24 A M) (x' : cart A M) : (term334 A M s x') = (term351 A M s x').
Proof. exact (MK_COMB (@lem8032361) (@lem8032360 A M s x')). Qed.
Lemma lem8032363 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term336 A M N s x' t) = (term352 A M N s x' t).
Proof. exact (MK_COMB (@lem8032362 A M s x') (@lem8032350 A N t)). Qed.
Lemma lem8032372 {A M : Type'} (x : cart A M) (x' : cart A M) : (term338 A M x x') = (term338 A M x x').
Proof. exact (eq_refl (term338 A M x x')). Qed.
Lemma lem8032373 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term340 A M N x s x' t) = (term353 A M N x s x' t).
Proof. exact (MK_COMB (@lem8032372 A M x x') (@lem8032363 A M N s x' t)). Qed.
Lemma lem8032374 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term346 A M N x s t) = (term354 A M N x s t).
Proof. exact (fun_ext (fun x' : cart A M => @lem8032373 A M N x s x' t)). Qed.
Lemma lem8032375 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8032376 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term347 A M N x s t) = (term355 A M N x s t).
Proof. exact (MK_COMB (@lem8032375 A M) (@lem8032374 A M N x s t)). Qed.
Lemma lem8032377 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) (h1 : term278 A M N x s t) : term355 A M N x s t.
Proof. exact (EQ_MP (@lem8032376 A M N x s t) (@lem8032326 A M N x s t h1)). Qed.
Lemma lem8032382 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8032383 {A M : Type'} (f : type24 A M) (x : cart A M) : (f x) = (@I ((cart A M) -> Prop) f x).
Proof. exact (@lem8032382 (cart A M) Prop f x). Qed.
Lemma lem8032385 {A M : Type'} (s : type24 A M) (x'' : cart A M) : (s x'') = (@I ((cart A M) -> Prop) s x'').
Proof. exact (@lem8032383 A M s x''). Qed.
Lemma lem8032390 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8032391 {A N : Type'} (f : type24 A N) (x : cart A N) : (f x) = (@I ((cart A N) -> Prop) f x).
Proof. exact (@lem8032390 (cart A N) Prop f x). Qed.
Lemma lem8032393 {A N : Type'} (t : type24 A N) (x' : cart A N) : (t x') = (@I ((cart A N) -> Prop) t x').
Proof. exact (@lem8032391 A N t x'). Qed.
Lemma lem8032394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8032395 {A N : Type'} (t : type24 A N) (x' : cart A N) : (term224 A N t x') = (term356 A N t x').
Proof. exact (MK_COMB (@lem8032394) (@lem8032393 A N t x')). Qed.
Lemma lem8032396 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) : (term316 A M N t x' s x'') = (term357 A M N t x' s x'').
Proof. exact (MK_COMB (@lem8032395 A N t x') (@lem8032385 A M s x'')). Qed.
Lemma lem8032405 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8032406 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) : (term322 A M N t x' s x'') = (term358 A M N t x' s x'').
Proof. exact (MK_COMB (@lem8032405 A M N s t) (@lem8032396 A M N t x' s x'')). Qed.
Lemma lem8032407 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term322 A M N t x' s x'') : term358 A M N t x' s x''.
Proof. exact (EQ_MP (@lem8032406 A M N t x' s x'') (@lem8032328 A M N t x' s x'' h1)). Qed.
Lemma lem8032408 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term322 A M N t x' s x'') : term357 A M N t x' s x''.
Proof. exact (proj2 (@lem8032407 A M N t x' s x'' h1)). Qed.
Lemma lem8032417 {A : Type'} (P : Prop) (Q : A -> Prop) : (term359 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem8032418 {A N : Type'} (P : Prop) (Q : type24 A N) : (term361 A N P Q) = (term362 A N P Q).
Proof. exact (@lem8032417 (cart A N) P Q). Qed.
Lemma lem8032419 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term363 A M N s x' t) = (term364 A M N s x' t).
Proof. exact (@lem8032418 A N (term348 A M s x') (term349 A N t)). Qed.
Lemma lem8032420 {A N : Type'} (t : type24 A N) (y : cart A N) : (term365 A N t y) = (term348 A N t y).
Proof. exact (eq_refl (term365 A N t y)). Qed.
Lemma lem8032421 {A N : Type'} (t : type24 A N) : (term366 A N t) = (term349 A N t).
Proof. exact (fun_ext (fun y : cart A N => @lem8032420 A N t y)). Qed.
Lemma lem8032422 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8032423 {A N : Type'} (t : type24 A N) : (term367 A N t) = (term350 A N t).
Proof. exact (MK_COMB (@lem8032422 A N) (@lem8032421 A N t)). Qed.
Lemma lem8032424 {A M : Type'} (s : type24 A M) (x' : cart A M) : (term351 A M s x') = (term351 A M s x').
Proof. exact (eq_refl (term351 A M s x')). Qed.
Lemma lem8032425 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term363 A M N s x' t) = (term352 A M N s x' t).
Proof. exact (MK_COMB (@lem8032424 A M s x') (@lem8032423 A N t)). Qed.
Lemma lem8032426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8032427 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term368 A M N s x' t) = (term369 A M N s x' t).
Proof. exact (MK_COMB (@lem8032426) (@lem8032425 A M N s x' t)). Qed.
Lemma lem8032428 {A N : Type'} (t : type24 A N) (y : cart A N) : (term365 A N t y) = (term348 A N t y).
Proof. exact (eq_refl (term365 A N t y)). Qed.
Lemma lem8032429 {A M : Type'} (s : type24 A M) (x' : cart A M) : (term351 A M s x') = (term351 A M s x').
Proof. exact (eq_refl (term351 A M s x')). Qed.
Lemma lem8032430 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term370 A M N s x' t y) = (term371 A M N s x' t y).
Proof. exact (MK_COMB (@lem8032429 A M s x') (@lem8032428 A N t y)). Qed.
Lemma lem8032431 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term372 A M N s x' t) = (term373 A M N s x' t).
Proof. exact (fun_ext (fun y : cart A N => @lem8032430 A M N s x' t y)). Qed.
Lemma lem8032432 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8032433 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term364 A M N s x' t) = (term374 A M N s x' t).
Proof. exact (MK_COMB (@lem8032432 A N) (@lem8032431 A M N s x' t)). Qed.
Lemma lem8032434 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : ((term363 A M N s x' t) = (term364 A M N s x' t)) = ((term352 A M N s x' t) = (term374 A M N s x' t)).
Proof. exact (MK_COMB (@lem8032427 A M N s x' t) (@lem8032433 A M N s x' t)). Qed.
Lemma lem8032435 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term352 A M N s x' t) = (term374 A M N s x' t).
Proof. exact (EQ_MP (@lem8032434 A M N s x' t) (@lem8032419 A M N s x' t)). Qed.
Lemma lem8032436 {A M : Type'} (x : cart A M) (x' : cart A M) : (term338 A M x x') = (term338 A M x x').
Proof. exact (eq_refl (term338 A M x x')). Qed.
Lemma lem8032437 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term353 A M N x s x' t) = (term375 A M N x s x' t).
Proof. exact (MK_COMB (@lem8032436 A M x x') (@lem8032435 A M N s x' t)). Qed.
Lemma lem8032439 {A : Type'} (P : Prop) (Q : A -> Prop) : (term359 A P Q) = (term360 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem8032440 {A N : Type'} (P : Prop) (Q : type24 A N) : (term361 A N P Q) = (term362 A N P Q).
Proof. exact (@lem8032439 (cart A N) P Q). Qed.
Lemma lem8032441 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term376 A M N x s x' t) = (term377 A M N x s x' t).
Proof. exact (@lem8032440 A N (term378 A M x x') (term373 A M N s x' t)). Qed.
Lemma lem8032442 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term379 A M N s x' t y) = (term371 A M N s x' t y).
Proof. exact (eq_refl (term379 A M N s x' t y)). Qed.
Lemma lem8032443 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term380 A M N s x' t) = (term373 A M N s x' t).
Proof. exact (fun_ext (fun y : cart A N => @lem8032442 A M N s x' t y)). Qed.
Lemma lem8032444 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8032445 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term381 A M N s x' t) = (term374 A M N s x' t).
Proof. exact (MK_COMB (@lem8032444 A N) (@lem8032443 A M N s x' t)). Qed.
Lemma lem8032446 {A M : Type'} (x : cart A M) (x' : cart A M) : (term338 A M x x') = (term338 A M x x').
Proof. exact (eq_refl (term338 A M x x')). Qed.
Lemma lem8032447 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term376 A M N x s x' t) = (term375 A M N x s x' t).
Proof. exact (MK_COMB (@lem8032446 A M x x') (@lem8032445 A M N s x' t)). Qed.
Lemma lem8032448 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8032449 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term382 A M N x s x' t) = (term383 A M N x s x' t).
Proof. exact (MK_COMB (@lem8032448) (@lem8032447 A M N x s x' t)). Qed.
Lemma lem8032450 {A M N : Type'} (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term379 A M N s x' t y) = (term371 A M N s x' t y).
Proof. exact (eq_refl (term379 A M N s x' t y)). Qed.
Lemma lem8032451 {A M : Type'} (x : cart A M) (x' : cart A M) : (term338 A M x x') = (term338 A M x x').
Proof. exact (eq_refl (term338 A M x x')). Qed.
Lemma lem8032452 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term384 A M N x s x' t y) = (term385 A M N x s x' t y).
Proof. exact (MK_COMB (@lem8032451 A M x x') (@lem8032450 A M N s x' t y)). Qed.
Lemma lem8032453 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term386 A M N x s x' t) = (term387 A M N x s x' t).
Proof. exact (fun_ext (fun y : cart A N => @lem8032452 A M N x s x' t y)). Qed.
Lemma lem8032454 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8032455 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term377 A M N x s x' t) = (term388 A M N x s x' t).
Proof. exact (MK_COMB (@lem8032454 A N) (@lem8032453 A M N x s x' t)). Qed.
Lemma lem8032456 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : ((term376 A M N x s x' t) = (term377 A M N x s x' t)) = ((term375 A M N x s x' t) = (term388 A M N x s x' t)).
Proof. exact (MK_COMB (@lem8032449 A M N x s x' t) (@lem8032455 A M N x s x' t)). Qed.
Lemma lem8032457 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term375 A M N x s x' t) = (term388 A M N x s x' t).
Proof. exact (EQ_MP (@lem8032456 A M N x s x' t) (@lem8032441 A M N x s x' t)). Qed.
Lemma lem8032458 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term353 A M N x s x' t) = (term388 A M N x s x' t).
Proof. exact (TRANS (@lem8032437 A M N x s x' t) (@lem8032457 A M N x s x' t)). Qed.
Lemma lem8032459 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term354 A M N x s t) = (term389 A M N x s t).
Proof. exact (fun_ext (fun x' : cart A M => @lem8032458 A M N x s x' t)). Qed.
Lemma lem8032460 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8032461 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term355 A M N x s t) = (term390 A M N x s t).
Proof. exact (MK_COMB (@lem8032460 A M) (@lem8032459 A M N x s t)). Qed.
Lemma lem8032474 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term385 A M N x s x' t y) = (term385 A M N x s x' t y).
Proof. exact (eq_refl (term385 A M N x s x' t y)). Qed.
Lemma lem8032475 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term387 A M N x s x' t) = (term387 A M N x s x' t).
Proof. exact (fun_ext (fun y : cart A N => @lem8032474 A M N x s x' t y)). Qed.
Lemma lem8032476 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8032477 {A M N : Type'} (x : cart A M) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term388 A M N x s x' t) = (term388 A M N x s x' t).
Proof. exact (MK_COMB (@lem8032476 A N) (@lem8032475 A M N x s x' t)). Qed.
Lemma lem8032478 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term389 A M N x s t) = (term389 A M N x s t).
Proof. exact (fun_ext (fun x' : cart A M => @lem8032477 A M N x s x' t)). Qed.
Lemma lem8032479 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8032480 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term390 A M N x s t) = (term390 A M N x s t).
Proof. exact (MK_COMB (@lem8032479 A M) (@lem8032478 A M N x s t)). Qed.
Lemma lem8032481 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) : (term355 A M N x s t) = (term390 A M N x s t).
Proof. exact (TRANS (@lem8032461 A M N x s t) (@lem8032480 A M N x s t)). Qed.
Lemma lem8032482 {A M N : Type'} (x : cart A M) (s : type24 A M) (t : type24 A N) (h1 : term278 A M N x s t) : term390 A M N x s t.
Proof. exact (EQ_MP (@lem8032481 A M N x s t) (@lem8032377 A M N x s t h1)). Qed.
Lemma lem8032495 {A M N : Type'} (_106037 : cart A M) (x : cart A M) (s : type24 A M) (t : type24 A N) (h1 : term278 A M N x s t) : term391 A M N x s t _106037.
Proof. exact (@lem8032482 A M N x s t h1 _106037). Qed.
Lemma lem8032496 {A M N : Type'} (x : cart A M) (s : type24 A M) (_106037 : cart A M) (t : type24 A N) : (term391 A M N x s t _106037) = (term388 A M N x s _106037 t).
Proof. exact (eq_refl (term391 A M N x s t _106037)). Qed.
Lemma lem8032497 {A M N : Type'} (_106037 : cart A M) (x : cart A M) (s : type24 A M) (t : type24 A N) (h1 : term278 A M N x s t) : term388 A M N x s _106037 t.
Proof. exact (EQ_MP (@lem8032496 A M N x s _106037 t) (@lem8032495 A M N _106037 x s t h1)). Qed.
Lemma lem8032498 {A M N : Type'} (_106037 : cart A M) (_106038 : cart A N) (x : cart A M) (s : type24 A M) (t : type24 A N) (h1 : term278 A M N x s t) : term392 A M N x s _106037 t _106038.
Proof. exact (@lem8032497 A M N _106037 x s t h1 _106038). Qed.
Lemma lem8032499 {A M N : Type'} (x : cart A M) (s : type24 A M) (_106037 : cart A M) (t : type24 A N) (_106038 : cart A N) : (term392 A M N x s _106037 t _106038) = (term385 A M N x s _106037 t _106038).
Proof. exact (eq_refl (term392 A M N x s _106037 t _106038)). Qed.
Lemma lem8032512 {A M N : Type'} (_106037 : cart A M) (_106038 : cart A N) (x : cart A M) (s : type24 A M) (t : type24 A N) (h1 : term278 A M N x s t) : term385 A M N x s _106037 t _106038.
Proof. exact (EQ_MP (@lem8032499 A M N x s _106037 t _106038) (@lem8032498 A M N _106037 _106038 x s t h1)). Qed.
Lemma lem8032595 {A M : Type'} (x : cart A M) : x = x.
Proof. exact (@lem21386 (cart A M) x). Qed.
Lemma lem8032596 {A M : Type'} (x : cart A M) : x = x.
Proof. exact (@lem8032595 A M x). Qed.
Lemma lem8032597 {A M : Type'} (x : cart A M) : term393 A M x.
Proof. exact (fun h0 : term394 A M x => @lem8032596 A M x). Qed.
Lemma lem8032599 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8032600 {A M : Type'} (x : cart A M) : (term393 A M x) = (x = x).
Proof. exact (@lem8032599 (x = x)). Qed.
Lemma lem8032601 {A M : Type'} (x : cart A M) : x = x.
Proof. exact (EQ_MP (@lem8032600 A M x) (@lem8032597 A M x)). Qed.
Lemma lem8032603 {A M : Type'} (s : type24 A M) (x : cart A M) (h1 : s x) : @I ((cart A M) -> Prop) s x.
Proof. exact (EQ_MP (@lem8032336 A M s x) (@lem8032236 A M s x h1)). Qed.
Lemma lem8032604 {A M : Type'} (s : type24 A M) (x : cart A M) (h1 : s x) : term396 A M s x.
Proof. exact (fun h0 : term348 A M s x => @lem8032603 A M s x h1). Qed.
Lemma lem8032606 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8032607 {A M : Type'} (s : type24 A M) (x : cart A M) : (term396 A M s x) = (@I ((cart A M) -> Prop) s x).
Proof. exact (@lem8032606 (@I ((cart A M) -> Prop) s x)). Qed.
Lemma lem8032608 {A M : Type'} (s : type24 A M) (x : cart A M) (h1 : s x) : @I ((cart A M) -> Prop) s x.
Proof. exact (EQ_MP (@lem8032607 A M s x) (@lem8032604 A M s x h1)). Qed.
Lemma lem8032610 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term322 A M N t x' s x'') : @I ((cart A N) -> Prop) t x'.
Proof. exact (proj1 (@lem8032408 A M N t x' s x'' h1)). Qed.
Lemma lem8032611 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term322 A M N t x' s x'') : term396 A N t x'.
Proof. exact (fun h0 : term348 A N t x' => @lem8032610 A M N t x' s x'' h1). Qed.
Lemma lem8032613 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8032614 {A N : Type'} (t : type24 A N) (x' : cart A N) : (term396 A N t x') = (@I ((cart A N) -> Prop) t x').
Proof. exact (@lem8032613 (@I ((cart A N) -> Prop) t x')). Qed.
Lemma lem8032615 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term322 A M N t x' s x'') : @I ((cart A N) -> Prop) t x'.
Proof. exact (EQ_MP (@lem8032614 A N t x') (@lem8032611 A M N t x' s x'' h1)). Qed.
Lemma lem8032617 (a : Prop) (b : Prop) : (term397 a b) = (term398 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem8032618 {A M N : Type'} (s : type24 A M) (_106037 : cart A M) (t : type24 A N) (_106038 : cart A N) : (term371 A M N s _106037 t _106038) = (term399 A M N s _106037 t _106038).
Proof. exact (@lem8032617 (@I ((cart A M) -> Prop) s _106037) (@I ((cart A N) -> Prop) t _106038)). Qed.
Lemma lem8032619 {A M : Type'} (x : cart A M) (_106037 : cart A M) : (term338 A M x _106037) = (term338 A M x _106037).
Proof. exact (eq_refl (term338 A M x _106037)). Qed.
Lemma lem8032620 {A M N : Type'} (x : cart A M) (s : type24 A M) (_106037 : cart A M) (t : type24 A N) (_106038 : cart A N) : (term385 A M N x s _106037 t _106038) = (term400 A M N x s _106037 t _106038).
Proof. exact (MK_COMB (@lem8032619 A M x _106037) (@lem8032618 A M N s _106037 t _106038)). Qed.
Lemma lem8032622 (a : Prop) (b : Prop) : (term397 a b) = (term398 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem8032623 {A M N : Type'} (x : cart A M) (s : type24 A M) (_106037 : cart A M) (t : type24 A N) (_106038 : cart A N) : (term400 A M N x s _106037 t _106038) = (term401 A M N x s _106037 t _106038).
Proof. exact (@lem8032622 (x = _106037) (term402 A M N s _106037 t _106038)). Qed.
Lemma lem8032624 {A M N : Type'} (x : cart A M) (s : type24 A M) (_106037 : cart A M) (t : type24 A N) (_106038 : cart A N) : (term385 A M N x s _106037 t _106038) = (term401 A M N x s _106037 t _106038).
Proof. exact (TRANS (@lem8032620 A M N x s _106037 t _106038) (@lem8032623 A M N x s _106037 t _106038)). Qed.
Lemma lem8032626 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8032627 {A M N : Type'} (x : cart A M) (s : type24 A M) (_106037 : cart A M) (t : type24 A N) (_106038 : cart A N) : (term401 A M N x s _106037 t _106038) = (term403 A M N x s _106037 t _106038).
Proof. exact (@lem8032626 (term404 A M N x s _106037 t _106038)). Qed.
Lemma lem8032628 {A M N : Type'} (x : cart A M) (s : type24 A M) (_106037 : cart A M) (t : type24 A N) (_106038 : cart A N) : (term385 A M N x s _106037 t _106038) = (term403 A M N x s _106037 t _106038).
Proof. exact (TRANS (@lem8032624 A M N x s _106037 t _106038) (@lem8032627 A M N x s _106037 t _106038)). Qed.
Lemma lem8032630 {A M N : Type'} (x : cart A M) (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : s x) (h2 : term322 A M N t x' s x'') : term402 A M N s x t x'.
Proof. exact (conj (@lem8032608 A M s x h1) (@lem8032615 A M N t x' s x'' h2)). Qed.
Lemma lem8032631 {A M N : Type'} (x : cart A M) (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : s x) (h2 : term322 A M N t x' s x'') : term405 A M N s x t x'.
Proof. exact (conj (@lem8032601 A M x) (@lem8032630 A M N x t x' s x'' h1 h2)). Qed.
Lemma lem8032633 {A M N : Type'} (_106037 : cart A M) (_106038 : cart A N) (x : cart A M) (s : type24 A M) (t : type24 A N) (h1 : term278 A M N x s t) : term403 A M N x s _106037 t _106038.
Proof. exact (EQ_MP (@lem8032628 A M N x s _106037 t _106038) (@lem8032512 A M N _106037 _106038 x s t h1)). Qed.
Lemma lem8032634 {A M N : Type'} (_106037 : cart A M) (_106038 : cart A N) (x : cart A M) (s : type24 A M) (t : type24 A N) (h1 : term278 A M N x s t) : term403 A M N x s _106037 t _106038.
Proof. exact (@lem8032633 A M N _106037 _106038 x s t h1). Qed.
Lemma lem8032635 {A M N : Type'} (x' : cart A N) (x : cart A M) (s : type24 A M) (t : type24 A N) (h1 : term278 A M N x s t) : term406 A M N s x t x'.
Proof. exact (@lem8032634 A M N x x' x s t h1). Qed.
Lemma lem8032638 {A M N : Type'} (x : cart A M) (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term278 A M N x s t) (h2 : s x) (h3 : term322 A M N t x' s x'') : False.
Proof. exact (@lem8032635 A M N x' x s t h1 (@lem8032631 A M N x t x' s x'' h2 h3)). Qed.
Lemma lem8032639 {A M N : Type'} (x : cart A M) (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term278 A M N x s t) (h2 : s x) (h3 : term322 A M N t x' s x'') : term407.
Proof. exact (fun h0 : ~ False => @lem8032638 A M N x t x' s x'' h1 h2 h3). Qed.
Lemma lem8032641 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8032642 : term407 = False.
Proof. exact (@lem8032641 False). Qed.
Lemma lem8032643 {A M N : Type'} (x : cart A M) (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term278 A M N x s t) (h2 : s x) (h3 : term322 A M N t x' s x'') : False.
Proof. exact (EQ_MP (@lem8032642) (@lem8032639 A M N x t x' s x'' h1 h2 h3)). Qed.
Lemma lem8032644 {A M N : Type'} (x' : cart A N) (t : type24 A N) (s : type24 A M) (x : cart A M) (h1 : term325 A M N t x' s) (h2 : term278 A M N x s t) (h3 : s x) : False.
Proof. exact (ex_elim (@lem8032327 A M N t x' s h1) (fun x'' : cart A M => fun h0 : term324 A M N t x' s x'' => @lem8032643 A M N x t x' s x'' h2 h3 h0)). Qed.
Lemma lem8032645 {A M N : Type'} (x : cart A M) (t : type24 A N) (s : type24 A M) (h1 : term278 A M N x s t) (h2 : s x) (h3 : term220 A M N t s) : False.
Proof. exact (ex_elim (@lem8032230 A M N t s h3) (fun x' : cart A N => fun h0 : term326 A M N t s x' => @lem8032644 A M N x' t s x h0 h1 h2)). Qed.
Lemma lem8032646 {A M N : Type'} (x : cart A M) (t : type24 A N) (s : type24 A M) (h1 : term278 A M N x s t) (h2 : s x) (h3 : term220 A M N t s) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem8032645 A M N x t s h1 h2 h3) (fun h4 : False => @lem8032236 A M s x h2)). Qed.
Lemma lem8032647 {A M N : Type'} (x : cart A M) (t : type24 A N) (s : type24 A M) (h1 : term278 A M N x s t) (h2 : s x) (h3 : term220 A M N t s) : False.
Proof. exact (EQ_MP (@lem8032646 A M N x t s h1 h2 h3) (@lem8032236 A M s x h2)). Qed.
Lemma lem8032648 {A M N : Type'} (x : cart A M) (t : type24 A N) (s : type24 A M) (h1 : term278 A M N x s t) (h2 : s x) (h3 : term220 A M N t s) : (term278 A M N x s t) = False.
Proof. exact (prop_ext (fun h4 : term278 A M N x s t => @lem8032647 A M N x t s h1 h2 h3) (fun h4 : False => @lem8032126 A M N x s t h1)). Qed.
Lemma lem8032649 {A M N : Type'} (x : cart A M) (t : type24 A N) (s : type24 A M) (h1 : term278 A M N x s t) (h2 : s x) (h3 : term220 A M N t s) : False.
Proof. exact (EQ_MP (@lem8032648 A M N x t s h1 h2 h3) (@lem8032126 A M N x s t h1)). Qed.
Lemma lem8032650 {A M N : Type'} (x : cart A M) (t : type24 A N) (s : type24 A M) (h1 : s x) (h2 : term220 A M N t s) : term277 A M N x s t.
Proof. exact (fun h0 : term278 A M N x s t => @lem8032649 A M N x t s h0 h1 h2). Qed.
Lemma lem8032651 {A M N : Type'} (x : cart A M) (t : type24 A N) (s : type24 A M) (h1 : s x) (h2 : term220 A M N t s) : term262 A M N x s t.
Proof. exact (EQ_MP (@lem8032125 A M N x s t) (@lem8032650 A M N x t s h1 h2)). Qed.
Lemma lem8032652 {A M N : Type'} (x : cart A M) (t : type24 A N) (s : type24 A M) (h1 : term220 A M N t s) : term263 A M N x s t.
Proof. exact (fun h0 : s x => @lem8032651 A M N x t s h0 h1). Qed.
Lemma lem8032657 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : term220 A M N t s) : term265 A M N s t.
Proof. exact (fun x : cart A M => @lem8032652 A M N x t s h1). Qed.
Lemma lem8032658 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term266 A M N s t.
Proof. exact (fun h0 : term220 A M N t s => @lem8032657 A M N t s h0). Qed.
Lemma lem8032663 {A M N : Type'} (t : type24 A N) : term270 A M N t.
Proof. exact (fun s : type24 A M => @lem8032658 A M N s t). Qed.
Lemma lem8032668 {A M N : Type'} : term274 A M N.
Proof. exact (fun t : type24 A N => @lem8032663 A M N t). Qed.
Lemma lem8032669 {A M N : Type'} : term273 A M N.
Proof. exact (EQ_MP (@lem8032119 A M N) (@lem8032668 A M N)). Qed.
Lemma lem8032670 {A M N : Type'} (t : type24 A N) : term408 A M N t.
Proof. exact (@lem8032669 A M N t). Qed.
Lemma lem8032671 {A M N : Type'} (t : type24 A N) : (term408 A M N t) = (term269 A M N t).
Proof. exact (eq_refl (term408 A M N t)). Qed.
Lemma lem8032672 {A M N : Type'} (t : type24 A N) : term269 A M N t.
Proof. exact (EQ_MP (@lem8032671 A M N t) (@lem8032670 A M N t)). Qed.
Lemma lem8032673 {A M N : Type'} (t : type24 A N) (s : type24 A M) : term409 A M N t s.
Proof. exact (@lem8032672 A M N t s). Qed.
Lemma lem8032674 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term409 A M N t s) = (term236 A M N s t).
Proof. exact (eq_refl (term409 A M N t s)). Qed.
Lemma lem8032675 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term236 A M N s t.
Proof. exact (EQ_MP (@lem8032674 A M N s t) (@lem8032673 A M N t s)). Qed.
Lemma lem8032677 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term236 A M N s t.
Proof. exact (@lem8031846 A M N s t (@lem8032675 A M N s t)). Qed.
Lemma lem8032678 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term237 A M N s t) : False.
Proof. exact (@lem8032677 A M N s t (@lem8031830 A M N s t h1)). Qed.
Lemma lem8032679 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term237 A M N s t) : (term237 A M N s t) = False.
Proof. exact (prop_ext (fun h2 : term237 A M N s t => @lem8032678 A M N s t h1) (fun h2 : False => @lem8031830 A M N s t h1)). Qed.
Lemma lem8032680 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term237 A M N s t) : False.
Proof. exact (EQ_MP (@lem8032679 A M N s t h1) (@lem8031830 A M N s t h1)). Qed.
Lemma lem8032681 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term236 A M N s t.
Proof. exact (fun h0 : term237 A M N s t => @lem8032680 A M N s t h0). Qed.
Lemma lem8032682 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term234 A M N s t.
Proof. exact (EQ_MP (@lem8031829 A M N s t) (@lem8032681 A M N s t)). Qed.
Lemma lem8032683 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term210 A M N s t.
Proof. exact (EQ_MP (@lem8031825 A M N s t) (@lem8032682 A M N s t)). Qed.
Lemma lem8032684 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term209 A M N s t.
Proof. exact (EQ_MP (@lem8031679 A M N s t) (@lem8032683 A M N s t)). Qed.
Lemma lem8032685 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) (h2 : term38 A M s) (h3 : term38 A N t) : term186 A M N s t.
Proof. exact (@lem8032684 A M N s t (@lem8031603 A M N s t h1 h2 h3)). Qed.
Lemma lem8032696 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A M s) (h2 : term38 A N t) : term196 A M N t s.
Proof. exact (conj (@lem8030219 A N t h2) (@lem8030214 A M s h1)). Qed.
Lemma lem8032697 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) (h2 : term38 A M s) (h3 : term38 A N t) : term197 A M N t s.
Proof. exact (conj (@lem8030694 A M N s t h1) (@lem8032696 A M N s t h2 h3)). Qed.
Lemma lem8032707 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term198 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8032708 {A N : Type'} (s : type24 A N) (t : type24 A N) : (s = t) = (term199 A N s t).
Proof. exact (@lem8032707 (cart A N) s t). Qed.
Lemma lem8032709 {A N : Type'} (t : type24 A N) : (t = (@EMPTY (cart A N))) = (term200 A N t).
Proof. exact (@lem8032708 A N t (@EMPTY (cart A N))). Qed.
Lemma lem8032718 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8032719 {A N : Type'} (t : type24 A N) : (term38 A N t) = (term201 A N t).
Proof. exact (MK_COMB (@lem8032718) (@lem8032709 A N t)). Qed.
Lemma lem8032720 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8032721 {A N : Type'} (t : type24 A N) : (term202 A N t) = (term203 A N t).
Proof. exact (MK_COMB (@lem8032720) (@lem8032719 A N t)). Qed.
Lemma lem8032725 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term198 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8032726 {A M : Type'} (s : type24 A M) (t : type24 A M) : (s = t) = (term199 A M s t).
Proof. exact (@lem8032725 (cart A M) s t). Qed.
Lemma lem8032727 {A M : Type'} (s : type24 A M) : (s = (@EMPTY (cart A M))) = (term200 A M s).
Proof. exact (@lem8032726 A M s (@EMPTY (cart A M))). Qed.
Lemma lem8032736 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8032737 {A M : Type'} (s : type24 A M) : (term38 A M s) = (term201 A M s).
Proof. exact (MK_COMB (@lem8032736) (@lem8032727 A M s)). Qed.
Lemma lem8032738 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term196 A M N t s) = (term204 A M N t s).
Proof. exact (MK_COMB (@lem8032721 A N t) (@lem8032737 A M s)). Qed.
Lemma lem8032741 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8032742 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term197 A M N t s) = (term206 A M N t s).
Proof. exact (MK_COMB (@lem8032741 A M N s t) (@lem8032738 A M N t s)). Qed.
Lemma lem8032745 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8032746 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term207 A M N t s) = (term208 A M N t s).
Proof. exact (MK_COMB (@lem8032745) (@lem8032742 A M N t s)). Qed.
Lemma lem8032769 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term195 A M N s t) = (term195 A M N s t).
Proof. exact (eq_refl (term195 A M N s t)). Qed.
Lemma lem8032770 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term410 A M N s t) = (term411 A M N s t).
Proof. exact (MK_COMB (@lem8032746 A M N t s) (@lem8032769 A M N s t)). Qed.
Lemma lem8032773 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term411 A M N s t) = (term410 A M N s t).
Proof. exact (SYM (@lem8032770 A M N s t)). Qed.
Lemma lem8032787 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8032788 {A N : Type'} (P : type24 A N) (x : cart A N) : (@IN (cart A N) x P) = (P x).
Proof. exact (@lem8032787 (cart A N) P x). Qed.
Lemma lem8032789 {A N : Type'} (t : type24 A N) (x : cart A N) : (@IN (cart A N) x t) = (t x).
Proof. exact (@lem8032788 A N t x). Qed.
Lemma lem8032790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8032791 {A N : Type'} (t : type24 A N) (x : cart A N) : (term211 A N x t) = (term212 A N t x).
Proof. exact (MK_COMB (@lem8032790) (@lem8032789 A N t x)). Qed.
Lemma lem8032793 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8032794 {A N : Type'} (x : cart A N) : (@IN (cart A N) x (@EMPTY (cart A N))) = False.
Proof. exact (@lem8032793 (cart A N) x). Qed.
Lemma lem8032795 {A N : Type'} (t : type24 A N) (x : cart A N) : ((@IN (cart A N) x t) = (@IN (cart A N) x (@EMPTY (cart A N)))) = ((t x) = False).
Proof. exact (MK_COMB (@lem8032791 A N t x) (@lem8032794 A N x)). Qed.
Lemma lem8032797 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8032798 {A N : Type'} (t : type24 A N) (x : cart A N) : ((t x) = False) = (term213 A N t x).
Proof. exact (@lem8032797 (t x)). Qed.
Lemma lem8032799 {A N : Type'} (t : type24 A N) (x : cart A N) : ((@IN (cart A N) x t) = (@IN (cart A N) x (@EMPTY (cart A N)))) = (term213 A N t x).
Proof. exact (TRANS (@lem8032795 A N t x) (@lem8032798 A N t x)). Qed.
Lemma lem8032800 {A N : Type'} (t : type24 A N) : (term214 A N t) = (term215 A N t).
Proof. exact (fun_ext (fun x : cart A N => @lem8032799 A N t x)). Qed.
Lemma lem8032801 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8032802 {A N : Type'} (t : type24 A N) : (term200 A N t) = (term216 A N t).
Proof. exact (MK_COMB (@lem8032801 A N) (@lem8032800 A N t)). Qed.
Lemma lem8032807 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8032808 {A N : Type'} (t : type24 A N) : (term201 A N t) = (term217 A N t).
Proof. exact (MK_COMB (@lem8032807) (@lem8032802 A N t)). Qed.
Lemma lem8032809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8032810 {A N : Type'} (t : type24 A N) : (term203 A N t) = (term218 A N t).
Proof. exact (MK_COMB (@lem8032809) (@lem8032808 A N t)). Qed.
Lemma lem8032818 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8032819 {A M : Type'} (P : type24 A M) (x : cart A M) : (@IN (cart A M) x P) = (P x).
Proof. exact (@lem8032818 (cart A M) P x). Qed.
Lemma lem8032820 {A M : Type'} (s : type24 A M) (x : cart A M) : (@IN (cart A M) x s) = (s x).
Proof. exact (@lem8032819 A M s x). Qed.
Lemma lem8032821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8032822 {A M : Type'} (s : type24 A M) (x : cart A M) : (term211 A M x s) = (term212 A M s x).
Proof. exact (MK_COMB (@lem8032821) (@lem8032820 A M s x)). Qed.
Lemma lem8032824 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8032825 {A M : Type'} (x : cart A M) : (@IN (cart A M) x (@EMPTY (cart A M))) = False.
Proof. exact (@lem8032824 (cart A M) x). Qed.
Lemma lem8032826 {A M : Type'} (s : type24 A M) (x : cart A M) : ((@IN (cart A M) x s) = (@IN (cart A M) x (@EMPTY (cart A M)))) = ((s x) = False).
Proof. exact (MK_COMB (@lem8032822 A M s x) (@lem8032825 A M x)). Qed.
Lemma lem8032828 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8032829 {A M : Type'} (s : type24 A M) (x : cart A M) : ((s x) = False) = (term213 A M s x).
Proof. exact (@lem8032828 (s x)). Qed.
Lemma lem8032830 {A M : Type'} (s : type24 A M) (x : cart A M) : ((@IN (cart A M) x s) = (@IN (cart A M) x (@EMPTY (cart A M)))) = (term213 A M s x).
Proof. exact (TRANS (@lem8032826 A M s x) (@lem8032829 A M s x)). Qed.
Lemma lem8032831 {A M : Type'} (s : type24 A M) : (term214 A M s) = (term215 A M s).
Proof. exact (fun_ext (fun x : cart A M => @lem8032830 A M s x)). Qed.
Lemma lem8032832 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8032833 {A M : Type'} (s : type24 A M) : (term200 A M s) = (term216 A M s).
Proof. exact (MK_COMB (@lem8032832 A M) (@lem8032831 A M s)). Qed.
Lemma lem8032838 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8032839 {A M : Type'} (s : type24 A M) : (term201 A M s) = (term217 A M s).
Proof. exact (MK_COMB (@lem8032838) (@lem8032833 A M s)). Qed.
Lemma lem8032840 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term204 A M N t s) = (term219 A M N t s).
Proof. exact (MK_COMB (@lem8032810 A N t) (@lem8032839 A M s)). Qed.
Lemma lem8032843 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8032844 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term206 A M N t s) = (term220 A M N t s).
Proof. exact (MK_COMB (@lem8032843 A M N s t) (@lem8032840 A M N t s)). Qed.
Lemma lem8032847 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8032848 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term208 A M N t s) = (term221 A M N t s).
Proof. exact (MK_COMB (@lem8032847) (@lem8032844 A M N t s)). Qed.
Lemma lem8032856 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8032857 {A N : Type'} (P : type24 A N) (x : cart A N) : (@IN (cart A N) x P) = (P x).
Proof. exact (@lem8032856 (cart A N) P x). Qed.
Lemma lem8032858 {A N : Type'} (t : type24 A N) (x : cart A N) : (@IN (cart A N) x t) = (t x).
Proof. exact (@lem8032857 A N t x). Qed.
Lemma lem8032859 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8032860 {A N : Type'} (t : type24 A N) (x : cart A N) : (term183 A N x t) = (term222 A N t x).
Proof. exact (MK_COMB (@lem8032859) (@lem8032858 A N t x)). Qed.
Lemma lem8032876 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8032877 {A M : Type'} (P : type24 A M) (x : cart A M) : (@IN (cart A M) x P) = (P x).
Proof. exact (@lem8032876 (cart A M) P x). Qed.
Lemma lem8032878 {A M : Type'} (s : type24 A M) (x : cart A M) : (@IN (cart A M) x s) = (s x).
Proof. exact (@lem8032877 A M s x). Qed.
Lemma lem8032879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8032880 {A M : Type'} (s : type24 A M) (x : cart A M) : (term223 A M x s) = (term224 A M s x).
Proof. exact (MK_COMB (@lem8032879) (@lem8032878 A M s x)). Qed.
Lemma lem8032882 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8032883 {A N : Type'} (P : type24 A N) (x : cart A N) : (@IN (cart A N) x P) = (P x).
Proof. exact (@lem8032882 (cart A N) P x). Qed.
Lemma lem8032884 {A N : Type'} (t : type24 A N) (y : cart A N) : (@IN (cart A N) y t) = (t y).
Proof. exact (@lem8032883 A N t y). Qed.
Lemma lem8032885 {A M N : Type'} (s : type24 A M) (x : cart A M) (t : type24 A N) (y : cart A N) : (term16 A M N x s y t) = (term225 A M N s x t y).
Proof. exact (MK_COMB (@lem8032880 A M s x) (@lem8032884 A N t y)). Qed.
Lemma lem8032888 {A N : Type'} (x : cart A N) (y : cart A N) : (term177 A N x y) = (term177 A N x y).
Proof. exact (eq_refl (term177 A N x y)). Qed.
Lemma lem8032889 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term188 A M N x x' s y t) = (term412 A M N x s x' t y).
Proof. exact (MK_COMB (@lem8032888 A N x y) (@lem8032885 A M N s x' t y)). Qed.
Lemma lem8032892 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term189 A M N x x' s t) = (term413 A M N x s x' t).
Proof. exact (fun_ext (fun y : cart A N => @lem8032889 A M N x s x' t y)). Qed.
Lemma lem8032893 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8032894 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term190 A M N x x' s t) = (term414 A M N x s x' t).
Proof. exact (MK_COMB (@lem8032893 A N) (@lem8032892 A M N x s x' t)). Qed.
Lemma lem8032899 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term191 A M N x s t) = (term415 A M N x s t).
Proof. exact (fun_ext (fun x' : cart A M => @lem8032894 A M N x s x' t)). Qed.
Lemma lem8032900 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8032901 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term192 A M N x s t) = (term416 A M N x s t).
Proof. exact (MK_COMB (@lem8032900 A M) (@lem8032899 A M N x s t)). Qed.
Lemma lem8032906 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term193 A M N x s t) = (term417 A M N x s t).
Proof. exact (MK_COMB (@lem8032860 A N t x) (@lem8032901 A M N x s t)). Qed.
Lemma lem8032909 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term194 A M N s t) = (term418 A M N s t).
Proof. exact (fun_ext (fun x : cart A N => @lem8032906 A M N x s t)). Qed.
Lemma lem8032910 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8032911 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term195 A M N s t) = (term419 A M N s t).
Proof. exact (MK_COMB (@lem8032910 A N) (@lem8032909 A M N s t)). Qed.
Lemma lem8032916 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term411 A M N s t) = (term420 A M N s t).
Proof. exact (MK_COMB (@lem8032848 A M N t s) (@lem8032911 A M N s t)). Qed.
Lemma lem8032919 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term420 A M N s t) = (term411 A M N s t).
Proof. exact (SYM (@lem8032916 A M N s t)). Qed.
Lemma lem8032921 (p : Prop) : p = (term235 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8032922 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term420 A M N s t) = (term421 A M N s t).
Proof. exact (@lem8032921 (term420 A M N s t)). Qed.
Lemma lem8032923 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term421 A M N s t) = (term420 A M N s t).
Proof. exact (SYM (@lem8032922 A M N s t)). Qed.
Lemma lem8032924 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term422 A M N s t) : term422 A M N s t.
Proof. exact (h1). Qed.
Lemma lem8032927 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term421 A M N s t) : term421 A M N s t.
Proof. exact (h1). Qed.
Lemma lem8032928 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term423 A M N s t.
Proof. exact (fun h0 : term421 A M N s t => @lem8032927 A M N s t h0). Qed.
Lemma lem8032929 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term423 A M N s t) : term423 A M N s t.
Proof. exact (h1). Qed.
Lemma lem8032930 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term421 A M N s t) : term421 A M N s t.
Proof. exact (h1). Qed.
Lemma lem8032931 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term421 A M N s t) (h2 : term423 A M N s t) : term421 A M N s t.
Proof. exact (@lem8032929 A M N s t h2 (@lem8032930 A M N s t h1)). Qed.
Lemma lem8032932 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term421 A M N s t) : term424 A M N s t.
Proof. exact (fun h0 : term423 A M N s t => @lem8032931 A M N s t h1 h0). Qed.
Lemma lem8032933 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term423 A M N s t) : term423 A M N s t.
Proof. exact (h1). Qed.
Lemma lem8032934 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term421 A M N s t) (h2 : term423 A M N s t) : term421 A M N s t.
Proof. exact (@lem8032932 A M N s t h1 (@lem8032933 A M N s t h2)). Qed.
Lemma lem8032935 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term423 A M N s t) : term423 A M N s t.
Proof. exact (fun h0 : term421 A M N s t => @lem8032934 A M N s t h0 h1). Qed.
Lemma lem8032936 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term425 A M N s t.
Proof. exact (fun h0 : term423 A M N s t => @lem8032935 A M N s t h0). Qed.
Lemma lem8032939 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term423 A M N s t.
Proof. exact (@lem8032936 A M N s t (@lem8032928 A M N s t)). Qed.
Lemma lem8032940 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term423 A M N s t.
Proof. exact (@lem8032939 A M N s t). Qed.
Lemma lem8032950 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8032951 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term421 A M N s t) = (term426 A M N s t).
Proof. exact (@lem8032950 (term422 A M N s t)). Qed.
Lemma lem8032953 (t : Prop) : (term242 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8032954 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term426 A M N s t) = (term420 A M N s t).
Proof. exact (@lem8032953 (term420 A M N s t)). Qed.
Lemma lem8032957 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term421 A M N s t) = (term420 A M N s t).
Proof. exact (TRANS (@lem8032951 A M N s t) (@lem8032954 A M N s t)). Qed.
Lemma lem8033032 {A M N : Type'} (t : type24 A N) : (term427 A M N t) = (term428 A M N t).
Proof. exact (fun_ext (fun s : type24 A M => @lem8032957 A M N s t)). Qed.
Lemma lem8033033 {A M : Type'} : (@all ((cart A M) -> Prop)) = (@all ((cart A M) -> Prop)).
Proof. exact (eq_refl (@all ((cart A M) -> Prop))). Qed.
Lemma lem8033034 {A M N : Type'} (t : type24 A N) : (term429 A M N t) = (term430 A M N t).
Proof. exact (MK_COMB (@lem8033033 A M) (@lem8033032 A M N t)). Qed.
Lemma lem8033039 {A M N : Type'} : (term431 A M N) = (term432 A M N).
Proof. exact (fun_ext (fun t : type24 A N => @lem8033034 A M N t)). Qed.
Lemma lem8033040 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem8033049 {A M N : Type'} : (term433 A M N) = (term434 A M N).
Proof. exact (MK_COMB (@lem8033040 A N) (@lem8033039 A M N)). Qed.
Lemma lem8033058 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term412 A M N x s x' t y) = (term412 A M N x s x' t y).
Proof. exact (eq_refl (term412 A M N x s x' t y)). Qed.
Lemma lem8033059 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term413 A M N x s x' t) = (term413 A M N x s x' t).
Proof. exact (fun_ext (fun y : cart A N => @lem8033058 A M N x s x' t y)). Qed.
Lemma lem8033060 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8033061 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term414 A M N x s x' t) = (term414 A M N x s x' t).
Proof. exact (MK_COMB (@lem8033060 A N) (@lem8033059 A M N x s x' t)). Qed.
Lemma lem8033062 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term415 A M N x s t) = (term415 A M N x s t).
Proof. exact (fun_ext (fun x' : cart A M => @lem8033061 A M N x s x' t)). Qed.
Lemma lem8033063 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8033064 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term416 A M N x s t) = (term416 A M N x s t).
Proof. exact (MK_COMB (@lem8033063 A M) (@lem8033062 A M N x s t)). Qed.
Lemma lem8033067 {A N : Type'} (t : type24 A N) (x : cart A N) : (term222 A N t x) = (term222 A N t x).
Proof. exact (eq_refl (term222 A N t x)). Qed.
Lemma lem8033068 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term417 A M N x s t) = (term417 A M N x s t).
Proof. exact (MK_COMB (@lem8033067 A N t x) (@lem8033064 A M N x s t)). Qed.
Lemma lem8033069 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term418 A M N s t) = (term418 A M N s t).
Proof. exact (fun_ext (fun x : cart A N => @lem8033068 A M N x s t)). Qed.
Lemma lem8033070 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8033071 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term419 A M N s t) = (term419 A M N s t).
Proof. exact (MK_COMB (@lem8033070 A N) (@lem8033069 A M N s t)). Qed.
Lemma lem8033074 {A M : Type'} (s : type24 A M) (x : cart A M) : (term213 A M s x) = (term213 A M s x).
Proof. exact (eq_refl (term213 A M s x)). Qed.
Lemma lem8033075 {A M : Type'} (s : type24 A M) : (term215 A M s) = (term215 A M s).
Proof. exact (fun_ext (fun x : cart A M => @lem8033074 A M s x)). Qed.
Lemma lem8033076 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8033077 {A M : Type'} (s : type24 A M) : (term216 A M s) = (term216 A M s).
Proof. exact (MK_COMB (@lem8033076 A M) (@lem8033075 A M s)). Qed.
Lemma lem8033078 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8033079 {A M : Type'} (s : type24 A M) : (term217 A M s) = (term217 A M s).
Proof. exact (MK_COMB (@lem8033078) (@lem8033077 A M s)). Qed.
Lemma lem8033082 {A N : Type'} (t : type24 A N) (x : cart A N) : (term213 A N t x) = (term213 A N t x).
Proof. exact (eq_refl (term213 A N t x)). Qed.
Lemma lem8033083 {A N : Type'} (t : type24 A N) : (term215 A N t) = (term215 A N t).
Proof. exact (fun_ext (fun x : cart A N => @lem8033082 A N t x)). Qed.
Lemma lem8033084 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8033085 {A N : Type'} (t : type24 A N) : (term216 A N t) = (term216 A N t).
Proof. exact (MK_COMB (@lem8033084 A N) (@lem8033083 A N t)). Qed.
Lemma lem8033086 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8033087 {A N : Type'} (t : type24 A N) : (term217 A N t) = (term217 A N t).
Proof. exact (MK_COMB (@lem8033086) (@lem8033085 A N t)). Qed.
Lemma lem8033088 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8033089 {A N : Type'} (t : type24 A N) : (term218 A N t) = (term218 A N t).
Proof. exact (MK_COMB (@lem8033088) (@lem8033087 A N t)). Qed.
Lemma lem8033090 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term219 A M N t s) = (term219 A M N t s).
Proof. exact (MK_COMB (@lem8033089 A N t) (@lem8033079 A M s)). Qed.
Lemma lem8033093 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8033094 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term220 A M N t s) = (term220 A M N t s).
Proof. exact (MK_COMB (@lem8033093 A M N s t) (@lem8033090 A M N t s)). Qed.
Lemma lem8033095 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8033096 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term221 A M N t s) = (term221 A M N t s).
Proof. exact (MK_COMB (@lem8033095) (@lem8033094 A M N t s)). Qed.
Lemma lem8033097 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term420 A M N s t) = (term420 A M N s t).
Proof. exact (MK_COMB (@lem8033096 A M N t s) (@lem8033071 A M N s t)). Qed.
Lemma lem8033098 {A M N : Type'} (t : type24 A N) : (term428 A M N t) = (term428 A M N t).
Proof. exact (fun_ext (fun s : type24 A M => @lem8033097 A M N s t)). Qed.
Lemma lem8033099 {A M : Type'} : (@all ((cart A M) -> Prop)) = (@all ((cart A M) -> Prop)).
Proof. exact (eq_refl (@all ((cart A M) -> Prop))). Qed.
Lemma lem8033100 {A M N : Type'} (t : type24 A N) : (term430 A M N t) = (term430 A M N t).
Proof. exact (MK_COMB (@lem8033099 A M) (@lem8033098 A M N t)). Qed.
Lemma lem8033101 {A M N : Type'} : (term432 A M N) = (term432 A M N).
Proof. exact (fun_ext (fun t : type24 A N => @lem8033100 A M N t)). Qed.
Lemma lem8033102 {A N : Type'} : (@all ((cart A N) -> Prop)) = (@all ((cart A N) -> Prop)).
Proof. exact (eq_refl (@all ((cart A N) -> Prop))). Qed.
Lemma lem8033103 {A M N : Type'} : (term434 A M N) = (term434 A M N).
Proof. exact (MK_COMB (@lem8033102 A N) (@lem8033101 A M N)). Qed.
Lemma lem8033160 {A M N : Type'} : (term433 A M N) = (term434 A M N).
Proof. exact (TRANS (@lem8033049 A M N) (@lem8033103 A M N)). Qed.
Lemma lem8033161 {A M N : Type'} : (term434 A M N) = (term433 A M N).
Proof. exact (SYM (@lem8033160 A M N)). Qed.
Lemma lem8033162 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : term220 A M N t s) : term220 A M N t s.
Proof. exact (h1). Qed.
Lemma lem8033165 (p : Prop) : p = (term235 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8033166 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term416 A M N x s t) = (term435 A M N x s t).
Proof. exact (@lem8033165 (term416 A M N x s t)). Qed.
Lemma lem8033167 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term435 A M N x s t) = (term416 A M N x s t).
Proof. exact (SYM (@lem8033166 A M N x s t)). Qed.
Lemma lem8033168 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) (h1 : term436 A M N x s t) : term436 A M N x s t.
Proof. exact (h1). Qed.
Lemma lem8033172 {A N : Type'} (t : type24 A N) (x : cart A N) : (term279 A N t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem8033173 {A N : Type'} (P : type24 A N) : (term280 A N P) = (term281 A N P).
Proof. exact (@lem18392 (cart A N) P). Qed.
Lemma lem8033174 {A N : Type'} (t : type24 A N) : (term217 A N t) = (term282 A N t).
Proof. exact (@lem8033173 A N (term215 A N t)). Qed.
Lemma lem8033175 {A N : Type'} (t : type24 A N) (x : cart A N) : (term283 A N t x) = (term213 A N t x).
Proof. exact (eq_refl (term283 A N t x)). Qed.
Lemma lem8033176 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8033177 {A N : Type'} (t : type24 A N) (x : cart A N) : (term284 A N t x) = (term279 A N t x).
Proof. exact (MK_COMB (@lem8033176) (@lem8033175 A N t x)). Qed.
Lemma lem8033178 {A N : Type'} (t : type24 A N) (x : cart A N) : (term284 A N t x) = (t x).
Proof. exact (TRANS (@lem8033177 A N t x) (@lem8033172 A N t x)). Qed.
Lemma lem8033179 {A N : Type'} (t : type24 A N) : (term285 A N t) = (term275 A N t).
Proof. exact (fun_ext (fun x : cart A N => @lem8033178 A N t x)). Qed.
Lemma lem8033180 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8033181 {A N : Type'} (t : type24 A N) : (term282 A N t) = (term276 A N t).
Proof. exact (MK_COMB (@lem8033180 A N) (@lem8033179 A N t)). Qed.
Lemma lem8033182 {A N : Type'} (t : type24 A N) : (term217 A N t) = (term276 A N t).
Proof. exact (TRANS (@lem8033174 A N t) (@lem8033181 A N t)). Qed.
Lemma lem8033185 {A M : Type'} (s : type24 A M) (x : cart A M) : (term279 A M s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem8033186 {A M : Type'} (P : type24 A M) : (term280 A M P) = (term281 A M P).
Proof. exact (@lem18392 (cart A M) P). Qed.
Lemma lem8033187 {A M : Type'} (s : type24 A M) : (term217 A M s) = (term282 A M s).
Proof. exact (@lem8033186 A M (term215 A M s)). Qed.
Lemma lem8033188 {A M : Type'} (s : type24 A M) (x : cart A M) : (term283 A M s x) = (term213 A M s x).
Proof. exact (eq_refl (term283 A M s x)). Qed.
Lemma lem8033189 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8033190 {A M : Type'} (s : type24 A M) (x : cart A M) : (term284 A M s x) = (term279 A M s x).
Proof. exact (MK_COMB (@lem8033189) (@lem8033188 A M s x)). Qed.
Lemma lem8033191 {A M : Type'} (s : type24 A M) (x : cart A M) : (term284 A M s x) = (s x).
Proof. exact (TRANS (@lem8033190 A M s x) (@lem8033185 A M s x)). Qed.
Lemma lem8033192 {A M : Type'} (s : type24 A M) : (term285 A M s) = (term275 A M s).
Proof. exact (fun_ext (fun x : cart A M => @lem8033191 A M s x)). Qed.
Lemma lem8033193 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8033194 {A M : Type'} (s : type24 A M) : (term282 A M s) = (term276 A M s).
Proof. exact (MK_COMB (@lem8033193 A M) (@lem8033192 A M s)). Qed.
Lemma lem8033195 {A M : Type'} (s : type24 A M) : (term217 A M s) = (term276 A M s).
Proof. exact (TRANS (@lem8033187 A M s) (@lem8033194 A M s)). Qed.
Lemma lem8033196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8033197 {A N : Type'} (t : type24 A N) : (term218 A N t) = (term286 A N t).
Proof. exact (MK_COMB (@lem8033196) (@lem8033182 A N t)). Qed.
Lemma lem8033198 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term219 A M N t s) = (term287 A M N t s).
Proof. exact (MK_COMB (@lem8033197 A N t) (@lem8033195 A M s)). Qed.
Lemma lem8033200 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8033201 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term220 A M N t s) = (term288 A M N t s).
Proof. exact (MK_COMB (@lem8033200 A M N s t) (@lem8033198 A M N t s)). Qed.
Lemma lem8033212 {A : Type'} (P : A -> Prop) (Q : Prop) : (term289 A P Q) = (term290 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8033213 {A N : Type'} (P : type24 A N) (Q : Prop) : (term291 A N P Q) = (term292 A N P Q).
Proof. exact (@lem8033212 (cart A N) P Q). Qed.
Lemma lem8033214 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term287 A M N t s) = (term293 A M N t s).
Proof. exact (@lem8033213 A N t (term276 A M s)). Qed.
Lemma lem8033216 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8033217 {A M : Type'} (P : Prop) (Q : type24 A M) : (term246 A M P Q) = (term245 A M P Q).
Proof. exact (@lem8033216 (cart A M) P Q). Qed.
Lemma lem8033218 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term294 A M N t x s) = (term295 A M N t x s).
Proof. exact (@lem8033217 A M (t x) s). Qed.
Lemma lem8033219 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term296 A M N t s) = (term297 A M N t s).
Proof. exact (fun_ext (fun x : cart A N => @lem8033218 A M N t x s)). Qed.
Lemma lem8033220 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8033221 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term293 A M N t s) = (term298 A M N t s).
Proof. exact (MK_COMB (@lem8033220 A N) (@lem8033219 A M N t s)). Qed.
Lemma lem8033222 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term287 A M N t s) = (term298 A M N t s).
Proof. exact (TRANS (@lem8033214 A M N t s) (@lem8033221 A M N t s)). Qed.
Lemma lem8033223 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8033224 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term288 A M N t s) = (term299 A M N t s).
Proof. exact (MK_COMB (@lem8033223 A M N s t) (@lem8033222 A M N t s)). Qed.
Lemma lem8033226 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8033227 {A N : Type'} (P : Prop) (Q : type24 A N) : (term246 A N P Q) = (term245 A N P Q).
Proof. exact (@lem8033226 (cart A N) P Q). Qed.
Lemma lem8033228 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term300 A M N t s) = (term301 A M N t s).
Proof. exact (@lem8033227 A N (term35 A M N s t) (term297 A M N t s)). Qed.
Lemma lem8033229 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term302 A M N t s x) = (term295 A M N t x s).
Proof. exact (eq_refl (term302 A M N t s x)). Qed.
Lemma lem8033230 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term303 A M N t s) = (term297 A M N t s).
Proof. exact (fun_ext (fun x : cart A N => @lem8033229 A M N t x s)). Qed.
Lemma lem8033231 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8033232 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term304 A M N t s) = (term298 A M N t s).
Proof. exact (MK_COMB (@lem8033231 A N) (@lem8033230 A M N t s)). Qed.
Lemma lem8033233 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8033234 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term300 A M N t s) = (term299 A M N t s).
Proof. exact (MK_COMB (@lem8033233 A M N s t) (@lem8033232 A M N t s)). Qed.
Lemma lem8033235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8033236 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term305 A M N t s) = (term306 A M N t s).
Proof. exact (MK_COMB (@lem8033235) (@lem8033234 A M N t s)). Qed.
Lemma lem8033237 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term302 A M N t s x) = (term295 A M N t x s).
Proof. exact (eq_refl (term302 A M N t s x)). Qed.
Lemma lem8033238 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8033239 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term307 A M N t s x) = (term308 A M N t x s).
Proof. exact (MK_COMB (@lem8033238 A M N s t) (@lem8033237 A M N t x s)). Qed.
Lemma lem8033240 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term309 A M N t s) = (term310 A M N t s).
Proof. exact (fun_ext (fun x : cart A N => @lem8033239 A M N t x s)). Qed.
Lemma lem8033241 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8033242 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term301 A M N t s) = (term311 A M N t s).
Proof. exact (MK_COMB (@lem8033241 A N) (@lem8033240 A M N t s)). Qed.
Lemma lem8033243 {A M N : Type'} (t : type24 A N) (s : type24 A M) : ((term300 A M N t s) = (term301 A M N t s)) = ((term299 A M N t s) = (term311 A M N t s)).
Proof. exact (MK_COMB (@lem8033236 A M N t s) (@lem8033242 A M N t s)). Qed.
Lemma lem8033244 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term299 A M N t s) = (term311 A M N t s).
Proof. exact (EQ_MP (@lem8033243 A M N t s) (@lem8033228 A M N t s)). Qed.
Lemma lem8033246 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term243 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8033247 {A M : Type'} (P : Prop) (Q : type24 A M) : (term246 A M P Q) = (term245 A M P Q).
Proof. exact (@lem8033246 (cart A M) P Q). Qed.
Lemma lem8033248 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term312 A M N t x s) = (term313 A M N t x s).
Proof. exact (@lem8033247 A M (term35 A M N s t) (term314 A M N t x s)). Qed.
Lemma lem8033249 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) (x' : cart A M) : (term315 A M N t x s x') = (term316 A M N t x s x').
Proof. exact (eq_refl (term315 A M N t x s x')). Qed.
Lemma lem8033250 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term317 A M N t x s) = (term314 A M N t x s).
Proof. exact (fun_ext (fun x' : cart A M => @lem8033249 A M N t x s x')). Qed.
Lemma lem8033251 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8033252 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term318 A M N t x s) = (term295 A M N t x s).
Proof. exact (MK_COMB (@lem8033251 A M) (@lem8033250 A M N t x s)). Qed.
Lemma lem8033253 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8033254 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term312 A M N t x s) = (term308 A M N t x s).
Proof. exact (MK_COMB (@lem8033253 A M N s t) (@lem8033252 A M N t x s)). Qed.
Lemma lem8033255 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8033256 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term319 A M N t x s) = (term320 A M N t x s).
Proof. exact (MK_COMB (@lem8033255) (@lem8033254 A M N t x s)). Qed.
Lemma lem8033257 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) (x' : cart A M) : (term315 A M N t x s x') = (term316 A M N t x s x').
Proof. exact (eq_refl (term315 A M N t x s x')). Qed.
Lemma lem8033258 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8033259 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) (x' : cart A M) : (term321 A M N t x s x') = (term322 A M N t x s x').
Proof. exact (MK_COMB (@lem8033258 A M N s t) (@lem8033257 A M N t x s x')). Qed.
Lemma lem8033260 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term323 A M N t x s) = (term324 A M N t x s).
Proof. exact (fun_ext (fun x' : cart A M => @lem8033259 A M N t x s x')). Qed.
Lemma lem8033261 {A M : Type'} : (@ex (cart A M)) = (@ex (cart A M)).
Proof. exact (eq_refl (@ex (cart A M))). Qed.
Lemma lem8033262 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term313 A M N t x s) = (term325 A M N t x s).
Proof. exact (MK_COMB (@lem8033261 A M) (@lem8033260 A M N t x s)). Qed.
Lemma lem8033263 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : ((term312 A M N t x s) = (term313 A M N t x s)) = ((term308 A M N t x s) = (term325 A M N t x s)).
Proof. exact (MK_COMB (@lem8033256 A M N t x s) (@lem8033262 A M N t x s)). Qed.
Lemma lem8033264 {A M N : Type'} (t : type24 A N) (x : cart A N) (s : type24 A M) : (term308 A M N t x s) = (term325 A M N t x s).
Proof. exact (EQ_MP (@lem8033263 A M N t x s) (@lem8033248 A M N t x s)). Qed.
Lemma lem8033265 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term310 A M N t s) = (term326 A M N t s).
Proof. exact (fun_ext (fun x : cart A N => @lem8033264 A M N t x s)). Qed.
Lemma lem8033266 {A N : Type'} : (@ex (cart A N)) = (@ex (cart A N)).
Proof. exact (eq_refl (@ex (cart A N))). Qed.
Lemma lem8033267 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term311 A M N t s) = (term327 A M N t s).
Proof. exact (MK_COMB (@lem8033266 A N) (@lem8033265 A M N t s)). Qed.
Lemma lem8033268 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term299 A M N t s) = (term327 A M N t s).
Proof. exact (TRANS (@lem8033244 A M N t s) (@lem8033267 A M N t s)). Qed.
Lemma lem8033270 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term288 A M N t s) = (term327 A M N t s).
Proof. exact (TRANS (@lem8033224 A M N t s) (@lem8033268 A M N t s)). Qed.
Lemma lem8033271 {A M N : Type'} (t : type24 A N) (s : type24 A M) : (term220 A M N t s) = (term327 A M N t s).
Proof. exact (TRANS (@lem8033201 A M N t s) (@lem8033270 A M N t s)). Qed.
Lemma lem8033272 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : term220 A M N t s) : term327 A M N t s.
Proof. exact (EQ_MP (@lem8033271 A M N t s) (@lem8033162 A M N t s h1)). Qed.
Lemma lem8033278 {A N : Type'} (t : type24 A N) (x : cart A N) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem8033286 {A M N : Type'} (s : type24 A M) (x : cart A M) (t : type24 A N) (y : cart A N) : (term437 A M N s x t y) = (term438 A M N s x t y).
Proof. exact (@lem17045 (s x) (t y)). Qed.
Lemma lem8033288 {A N : Type'} (x : cart A N) (y : cart A N) : (term338 A N x y) = (term338 A N x y).
Proof. exact (eq_refl (term338 A N x y)). Qed.
Lemma lem8033289 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term439 A M N x s x' t y) = (term440 A M N x s x' t y).
Proof. exact (MK_COMB (@lem8033288 A N x y) (@lem8033286 A M N s x' t y)). Qed.
Lemma lem8033290 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term441 A M N x s x' t y) = (term439 A M N x s x' t y).
Proof. exact (@lem17045 (x = y) (term225 A M N s x' t y)). Qed.
Lemma lem8033291 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term441 A M N x s x' t y) = (term440 A M N x s x' t y).
Proof. exact (TRANS (@lem8033290 A M N x s x' t y) (@lem8033289 A M N x s x' t y)). Qed.
Lemma lem8033292 {A N : Type'} (P : type24 A N) : (term328 A N P) = (term216 A N P).
Proof. exact (@lem18394 (cart A N) P). Qed.
Lemma lem8033293 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term442 A M N x s x' t) = (term443 A M N x s x' t).
Proof. exact (@lem8033292 A N (term413 A M N x s x' t)). Qed.
Lemma lem8033294 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term444 A M N x s x' t y) = (term412 A M N x s x' t y).
Proof. exact (eq_refl (term444 A M N x s x' t y)). Qed.
Lemma lem8033295 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8033296 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term445 A M N x s x' t y) = (term441 A M N x s x' t y).
Proof. exact (MK_COMB (@lem8033295) (@lem8033294 A M N x s x' t y)). Qed.
Lemma lem8033297 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term445 A M N x s x' t y) = (term440 A M N x s x' t y).
Proof. exact (TRANS (@lem8033296 A M N x s x' t y) (@lem8033291 A M N x s x' t y)). Qed.
Lemma lem8033298 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term446 A M N x s x' t) = (term447 A M N x s x' t).
Proof. exact (fun_ext (fun y : cart A N => @lem8033297 A M N x s x' t y)). Qed.
Lemma lem8033299 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8033300 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term443 A M N x s x' t) = (term448 A M N x s x' t).
Proof. exact (MK_COMB (@lem8033299 A N) (@lem8033298 A M N x s x' t)). Qed.
Lemma lem8033301 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term442 A M N x s x' t) = (term448 A M N x s x' t).
Proof. exact (TRANS (@lem8033293 A M N x s x' t) (@lem8033300 A M N x s x' t)). Qed.
Lemma lem8033302 {A M : Type'} (P : type24 A M) : (term328 A M P) = (term216 A M P).
Proof. exact (@lem18394 (cart A M) P). Qed.
Lemma lem8033303 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term436 A M N x s t) = (term449 A M N x s t).
Proof. exact (@lem8033302 A M (term415 A M N x s t)). Qed.
Lemma lem8033304 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term450 A M N x s t x') = (term414 A M N x s x' t).
Proof. exact (eq_refl (term450 A M N x s t x')). Qed.
Lemma lem8033305 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8033306 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term451 A M N x s t x') = (term442 A M N x s x' t).
Proof. exact (MK_COMB (@lem8033305) (@lem8033304 A M N x s x' t)). Qed.
Lemma lem8033307 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term451 A M N x s t x') = (term448 A M N x s x' t).
Proof. exact (TRANS (@lem8033306 A M N x s x' t) (@lem8033301 A M N x s x' t)). Qed.
Lemma lem8033308 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term452 A M N x s t) = (term453 A M N x s t).
Proof. exact (fun_ext (fun x' : cart A M => @lem8033307 A M N x s x' t)). Qed.
Lemma lem8033309 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8033310 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term449 A M N x s t) = (term454 A M N x s t).
Proof. exact (MK_COMB (@lem8033309 A M) (@lem8033308 A M N x s t)). Qed.
Lemma lem8033367 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term436 A M N x s t) = (term454 A M N x s t).
Proof. exact (TRANS (@lem8033303 A M N x s t) (@lem8033310 A M N x s t)). Qed.
Lemma lem8033368 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) (h1 : term436 A M N x s t) : term454 A M N x s t.
Proof. exact (EQ_MP (@lem8033367 A M N x s t) (@lem8033168 A M N x s t h1)). Qed.
Lemma lem8033369 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (h1 : term325 A M N t x' s) : term325 A M N t x' s.
Proof. exact (h1). Qed.
Lemma lem8033370 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term322 A M N t x' s x'') : term322 A M N t x' s x''.
Proof. exact (h1). Qed.
Lemma lem8033375 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8033376 {A N : Type'} (f : type24 A N) (x : cart A N) : (f x) = (@I ((cart A N) -> Prop) f x).
Proof. exact (@lem8033375 (cart A N) Prop f x). Qed.
Lemma lem8033378 {A N : Type'} (t : type24 A N) (x : cart A N) : (t x) = (@I ((cart A N) -> Prop) t x).
Proof. exact (@lem8033376 A N t x). Qed.
Lemma lem8033380 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8033385 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8033386 {A N : Type'} (f : type24 A N) (x : cart A N) : (f x) = (@I ((cart A N) -> Prop) f x).
Proof. exact (@lem8033385 (cart A N) Prop f x). Qed.
Lemma lem8033388 {A N : Type'} (t : type24 A N) (y : cart A N) : (t y) = (@I ((cart A N) -> Prop) t y).
Proof. exact (@lem8033386 A N t y). Qed.
Lemma lem8033389 {A N : Type'} (t : type24 A N) (y : cart A N) : (term213 A N t y) = (term348 A N t y).
Proof. exact (MK_COMB (@lem8033380) (@lem8033388 A N t y)). Qed.
Lemma lem8033390 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8033395 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8033396 {A M : Type'} (f : type24 A M) (x : cart A M) : (f x) = (@I ((cart A M) -> Prop) f x).
Proof. exact (@lem8033395 (cart A M) Prop f x). Qed.
Lemma lem8033398 {A M : Type'} (s : type24 A M) (x : cart A M) : (s x) = (@I ((cart A M) -> Prop) s x).
Proof. exact (@lem8033396 A M s x). Qed.
Lemma lem8033399 {A M : Type'} (s : type24 A M) (x : cart A M) : (term213 A M s x) = (term348 A M s x).
Proof. exact (MK_COMB (@lem8033390) (@lem8033398 A M s x)). Qed.
Lemma lem8033400 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8033401 {A M : Type'} (s : type24 A M) (x : cart A M) : (term334 A M s x) = (term351 A M s x).
Proof. exact (MK_COMB (@lem8033400) (@lem8033399 A M s x)). Qed.
Lemma lem8033402 {A M N : Type'} (s : type24 A M) (x : cart A M) (t : type24 A N) (y : cart A N) : (term438 A M N s x t y) = (term371 A M N s x t y).
Proof. exact (MK_COMB (@lem8033401 A M s x) (@lem8033389 A N t y)). Qed.
Lemma lem8033411 {A N : Type'} (x : cart A N) (y : cart A N) : (term338 A N x y) = (term338 A N x y).
Proof. exact (eq_refl (term338 A N x y)). Qed.
Lemma lem8033412 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term440 A M N x s x' t y) = (term455 A M N x s x' t y).
Proof. exact (MK_COMB (@lem8033411 A N x y) (@lem8033402 A M N s x' t y)). Qed.
Lemma lem8033413 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term447 A M N x s x' t) = (term456 A M N x s x' t).
Proof. exact (fun_ext (fun y : cart A N => @lem8033412 A M N x s x' t y)). Qed.
Lemma lem8033414 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8033415 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term448 A M N x s x' t) = (term457 A M N x s x' t).
Proof. exact (MK_COMB (@lem8033414 A N) (@lem8033413 A M N x s x' t)). Qed.
Lemma lem8033416 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term453 A M N x s t) = (term458 A M N x s t).
Proof. exact (fun_ext (fun x' : cart A M => @lem8033415 A M N x s x' t)). Qed.
Lemma lem8033417 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8033418 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term454 A M N x s t) = (term459 A M N x s t).
Proof. exact (MK_COMB (@lem8033417 A M) (@lem8033416 A M N x s t)). Qed.
Lemma lem8033419 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) (h1 : term436 A M N x s t) : term459 A M N x s t.
Proof. exact (EQ_MP (@lem8033418 A M N x s t) (@lem8033368 A M N x s t h1)). Qed.
Lemma lem8033424 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8033425 {A M : Type'} (f : type24 A M) (x : cart A M) : (f x) = (@I ((cart A M) -> Prop) f x).
Proof. exact (@lem8033424 (cart A M) Prop f x). Qed.
Lemma lem8033427 {A M : Type'} (s : type24 A M) (x'' : cart A M) : (s x'') = (@I ((cart A M) -> Prop) s x'').
Proof. exact (@lem8033425 A M s x''). Qed.
Lemma lem8033432 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8033433 {A N : Type'} (f : type24 A N) (x : cart A N) : (f x) = (@I ((cart A N) -> Prop) f x).
Proof. exact (@lem8033432 (cart A N) Prop f x). Qed.
Lemma lem8033435 {A N : Type'} (t : type24 A N) (x' : cart A N) : (t x') = (@I ((cart A N) -> Prop) t x').
Proof. exact (@lem8033433 A N t x'). Qed.
Lemma lem8033436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8033437 {A N : Type'} (t : type24 A N) (x' : cart A N) : (term224 A N t x') = (term356 A N t x').
Proof. exact (MK_COMB (@lem8033436) (@lem8033435 A N t x')). Qed.
Lemma lem8033438 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) : (term316 A M N t x' s x'') = (term357 A M N t x' s x'').
Proof. exact (MK_COMB (@lem8033437 A N t x') (@lem8033427 A M s x'')). Qed.
Lemma lem8033447 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term205 A M N s t) = (term205 A M N s t).
Proof. exact (eq_refl (term205 A M N s t)). Qed.
Lemma lem8033448 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) : (term322 A M N t x' s x'') = (term358 A M N t x' s x'').
Proof. exact (MK_COMB (@lem8033447 A M N s t) (@lem8033438 A M N t x' s x'')). Qed.
Lemma lem8033449 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term322 A M N t x' s x'') : term358 A M N t x' s x''.
Proof. exact (EQ_MP (@lem8033448 A M N t x' s x'') (@lem8033370 A M N t x' s x'' h1)). Qed.
Lemma lem8033450 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term322 A M N t x' s x'') : term357 A M N t x' s x''.
Proof. exact (proj2 (@lem8033449 A M N t x' s x'' h1)). Qed.
Lemma lem8033471 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) (y : cart A N) : (term455 A M N x s x' t y) = (term455 A M N x s x' t y).
Proof. exact (eq_refl (term455 A M N x s x' t y)). Qed.
Lemma lem8033472 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term456 A M N x s x' t) = (term456 A M N x s x' t).
Proof. exact (fun_ext (fun y : cart A N => @lem8033471 A M N x s x' t y)). Qed.
Lemma lem8033473 {A N : Type'} : (@all (cart A N)) = (@all (cart A N)).
Proof. exact (eq_refl (@all (cart A N))). Qed.
Lemma lem8033474 {A M N : Type'} (x : cart A N) (s : type24 A M) (x' : cart A M) (t : type24 A N) : (term457 A M N x s x' t) = (term457 A M N x s x' t).
Proof. exact (MK_COMB (@lem8033473 A N) (@lem8033472 A M N x s x' t)). Qed.
Lemma lem8033475 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term458 A M N x s t) = (term458 A M N x s t).
Proof. exact (fun_ext (fun x' : cart A M => @lem8033474 A M N x s x' t)). Qed.
Lemma lem8033476 {A M : Type'} : (@all (cart A M)) = (@all (cart A M)).
Proof. exact (eq_refl (@all (cart A M))). Qed.
Lemma lem8033478 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) : (term459 A M N x s t) = (term459 A M N x s t).
Proof. exact (MK_COMB (@lem8033476 A M) (@lem8033475 A M N x s t)). Qed.
Lemma lem8033479 {A M N : Type'} (x : cart A N) (s : type24 A M) (t : type24 A N) (h1 : term436 A M N x s t) : term459 A M N x s t.
Proof. exact (EQ_MP (@lem8033478 A M N x s t) (@lem8033419 A M N x s t h1)). Qed.
Lemma lem8033492 {A M N : Type'} (_106053 : cart A M) (x : cart A N) (s : type24 A M) (t : type24 A N) (h1 : term436 A M N x s t) : term460 A M N x s t _106053.
Proof. exact (@lem8033479 A M N x s t h1 _106053). Qed.
Lemma lem8033493 {A M N : Type'} (x : cart A N) (s : type24 A M) (_106053 : cart A M) (t : type24 A N) : (term460 A M N x s t _106053) = (term457 A M N x s _106053 t).
Proof. exact (eq_refl (term460 A M N x s t _106053)). Qed.
Lemma lem8033494 {A M N : Type'} (_106053 : cart A M) (x : cart A N) (s : type24 A M) (t : type24 A N) (h1 : term436 A M N x s t) : term457 A M N x s _106053 t.
Proof. exact (EQ_MP (@lem8033493 A M N x s _106053 t) (@lem8033492 A M N _106053 x s t h1)). Qed.
Lemma lem8033495 {A M N : Type'} (_106053 : cart A M) (_106054 : cart A N) (x : cart A N) (s : type24 A M) (t : type24 A N) (h1 : term436 A M N x s t) : term461 A M N x s _106053 t _106054.
Proof. exact (@lem8033494 A M N _106053 x s t h1 _106054). Qed.
Lemma lem8033496 {A M N : Type'} (x : cart A N) (s : type24 A M) (_106053 : cart A M) (t : type24 A N) (_106054 : cart A N) : (term461 A M N x s _106053 t _106054) = (term455 A M N x s _106053 t _106054).
Proof. exact (eq_refl (term461 A M N x s _106053 t _106054)). Qed.
Lemma lem8033509 {A M N : Type'} (_106053 : cart A M) (_106054 : cart A N) (x : cart A N) (s : type24 A M) (t : type24 A N) (h1 : term436 A M N x s t) : term455 A M N x s _106053 t _106054.
Proof. exact (EQ_MP (@lem8033496 A M N x s _106053 t _106054) (@lem8033495 A M N _106053 _106054 x s t h1)). Qed.
Lemma lem8033592 {A N : Type'} (x : cart A N) : x = x.
Proof. exact (@lem21386 (cart A N) x). Qed.
Lemma lem8033593 {A N : Type'} (x : cart A N) : x = x.
Proof. exact (@lem8033592 A N x). Qed.
Lemma lem8033594 {A N : Type'} (x : cart A N) : term393 A N x.
Proof. exact (fun h0 : term394 A N x => @lem8033593 A N x). Qed.
Lemma lem8033596 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8033597 {A N : Type'} (x : cart A N) : (term393 A N x) = (x = x).
Proof. exact (@lem8033596 (x = x)). Qed.
Lemma lem8033598 {A N : Type'} (x : cart A N) : x = x.
Proof. exact (EQ_MP (@lem8033597 A N x) (@lem8033594 A N x)). Qed.
Lemma lem8033600 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term322 A M N t x' s x'') : @I ((cart A M) -> Prop) s x''.
Proof. exact (proj2 (@lem8033450 A M N t x' s x'' h1)). Qed.
Lemma lem8033601 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term322 A M N t x' s x'') : term396 A M s x''.
Proof. exact (fun h0 : term348 A M s x'' => @lem8033600 A M N t x' s x'' h1). Qed.
Lemma lem8033603 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8033604 {A M : Type'} (s : type24 A M) (x'' : cart A M) : (term396 A M s x'') = (@I ((cart A M) -> Prop) s x'').
Proof. exact (@lem8033603 (@I ((cart A M) -> Prop) s x'')). Qed.
Lemma lem8033605 {A M N : Type'} (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term322 A M N t x' s x'') : @I ((cart A M) -> Prop) s x''.
Proof. exact (EQ_MP (@lem8033604 A M s x'') (@lem8033601 A M N t x' s x'' h1)). Qed.
Lemma lem8033607 {A N : Type'} (t : type24 A N) (x : cart A N) (h1 : t x) : @I ((cart A N) -> Prop) t x.
Proof. exact (EQ_MP (@lem8033378 A N t x) (@lem8033278 A N t x h1)). Qed.
Lemma lem8033608 {A N : Type'} (t : type24 A N) (x : cart A N) (h1 : t x) : term396 A N t x.
Proof. exact (fun h0 : term348 A N t x => @lem8033607 A N t x h1). Qed.
Lemma lem8033610 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8033611 {A N : Type'} (t : type24 A N) (x : cart A N) : (term396 A N t x) = (@I ((cart A N) -> Prop) t x).
Proof. exact (@lem8033610 (@I ((cart A N) -> Prop) t x)). Qed.
Lemma lem8033612 {A N : Type'} (t : type24 A N) (x : cart A N) (h1 : t x) : @I ((cart A N) -> Prop) t x.
Proof. exact (EQ_MP (@lem8033611 A N t x) (@lem8033608 A N t x h1)). Qed.
Lemma lem8033614 (a : Prop) (b : Prop) : (term397 a b) = (term398 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem8033615 {A M N : Type'} (s : type24 A M) (_106053 : cart A M) (t : type24 A N) (_106054 : cart A N) : (term371 A M N s _106053 t _106054) = (term399 A M N s _106053 t _106054).
Proof. exact (@lem8033614 (@I ((cart A M) -> Prop) s _106053) (@I ((cart A N) -> Prop) t _106054)). Qed.
Lemma lem8033616 {A N : Type'} (x : cart A N) (_106054 : cart A N) : (term338 A N x _106054) = (term338 A N x _106054).
Proof. exact (eq_refl (term338 A N x _106054)). Qed.
Lemma lem8033617 {A M N : Type'} (x : cart A N) (s : type24 A M) (_106053 : cart A M) (t : type24 A N) (_106054 : cart A N) : (term455 A M N x s _106053 t _106054) = (term462 A M N x s _106053 t _106054).
Proof. exact (MK_COMB (@lem8033616 A N x _106054) (@lem8033615 A M N s _106053 t _106054)). Qed.
Lemma lem8033619 (a : Prop) (b : Prop) : (term397 a b) = (term398 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem8033620 {A M N : Type'} (x : cart A N) (s : type24 A M) (_106053 : cart A M) (t : type24 A N) (_106054 : cart A N) : (term462 A M N x s _106053 t _106054) = (term463 A M N x s _106053 t _106054).
Proof. exact (@lem8033619 (x = _106054) (term402 A M N s _106053 t _106054)). Qed.
Lemma lem8033621 {A M N : Type'} (x : cart A N) (s : type24 A M) (_106053 : cart A M) (t : type24 A N) (_106054 : cart A N) : (term455 A M N x s _106053 t _106054) = (term463 A M N x s _106053 t _106054).
Proof. exact (TRANS (@lem8033617 A M N x s _106053 t _106054) (@lem8033620 A M N x s _106053 t _106054)). Qed.
Lemma lem8033623 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8033624 {A M N : Type'} (x : cart A N) (s : type24 A M) (_106053 : cart A M) (t : type24 A N) (_106054 : cart A N) : (term463 A M N x s _106053 t _106054) = (term464 A M N x s _106053 t _106054).
Proof. exact (@lem8033623 (term465 A M N x s _106053 t _106054)). Qed.
Lemma lem8033625 {A M N : Type'} (x : cart A N) (s : type24 A M) (_106053 : cart A M) (t : type24 A N) (_106054 : cart A N) : (term455 A M N x s _106053 t _106054) = (term464 A M N x s _106053 t _106054).
Proof. exact (TRANS (@lem8033621 A M N x s _106053 t _106054) (@lem8033624 A M N x s _106053 t _106054)). Qed.
Lemma lem8033627 {A M N : Type'} (x : cart A N) (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : t x) (h2 : term322 A M N t x' s x'') : term402 A M N s x'' t x.
Proof. exact (conj (@lem8033605 A M N t x' s x'' h2) (@lem8033612 A N t x h1)). Qed.
Lemma lem8033628 {A M N : Type'} (x : cart A N) (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : t x) (h2 : term322 A M N t x' s x'') : term466 A M N s x'' t x.
Proof. exact (conj (@lem8033598 A N x) (@lem8033627 A M N x t x' s x'' h1 h2)). Qed.
Lemma lem8033630 {A M N : Type'} (_106053 : cart A M) (_106054 : cart A N) (x : cart A N) (s : type24 A M) (t : type24 A N) (h1 : term436 A M N x s t) : term464 A M N x s _106053 t _106054.
Proof. exact (EQ_MP (@lem8033625 A M N x s _106053 t _106054) (@lem8033509 A M N _106053 _106054 x s t h1)). Qed.
Lemma lem8033631 {A M N : Type'} (_106053 : cart A M) (_106054 : cart A N) (x : cart A N) (s : type24 A M) (t : type24 A N) (h1 : term436 A M N x s t) : term464 A M N x s _106053 t _106054.
Proof. exact (@lem8033630 A M N _106053 _106054 x s t h1). Qed.
Lemma lem8033632 {A M N : Type'} (x'' : cart A M) (x : cart A N) (s : type24 A M) (t : type24 A N) (h1 : term436 A M N x s t) : term467 A M N s x'' t x.
Proof. exact (@lem8033631 A M N x'' x x s t h1). Qed.
Lemma lem8033635 {A M N : Type'} (x : cart A N) (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term436 A M N x s t) (h2 : t x) (h3 : term322 A M N t x' s x'') : False.
Proof. exact (@lem8033632 A M N x'' x s t h1 (@lem8033628 A M N x t x' s x'' h2 h3)). Qed.
Lemma lem8033636 {A M N : Type'} (x : cart A N) (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term436 A M N x s t) (h2 : t x) (h3 : term322 A M N t x' s x'') : term407.
Proof. exact (fun h0 : ~ False => @lem8033635 A M N x t x' s x'' h1 h2 h3). Qed.
Lemma lem8033638 (p : Prop) : (term395 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8033639 : term407 = False.
Proof. exact (@lem8033638 False). Qed.
Lemma lem8033640 {A M N : Type'} (x : cart A N) (t : type24 A N) (x' : cart A N) (s : type24 A M) (x'' : cart A M) (h1 : term436 A M N x s t) (h2 : t x) (h3 : term322 A M N t x' s x'') : False.
Proof. exact (EQ_MP (@lem8033639) (@lem8033636 A M N x t x' s x'' h1 h2 h3)). Qed.
Lemma lem8033641 {A M N : Type'} (x' : cart A N) (s : type24 A M) (t : type24 A N) (x : cart A N) (h1 : term325 A M N t x' s) (h2 : term436 A M N x s t) (h3 : t x) : False.
Proof. exact (ex_elim (@lem8033369 A M N t x' s h1) (fun x'' : cart A M => fun h0 : term324 A M N t x' s x'' => @lem8033640 A M N x t x' s x'' h2 h3 h0)). Qed.
Lemma lem8033642 {A M N : Type'} (x : cart A N) (t : type24 A N) (s : type24 A M) (h1 : term436 A M N x s t) (h2 : t x) (h3 : term220 A M N t s) : False.
Proof. exact (ex_elim (@lem8033272 A M N t s h3) (fun x' : cart A N => fun h0 : term326 A M N t s x' => @lem8033641 A M N x' s t x h0 h1 h2)). Qed.
Lemma lem8033643 {A M N : Type'} (x : cart A N) (t : type24 A N) (s : type24 A M) (h1 : term436 A M N x s t) (h2 : t x) (h3 : term220 A M N t s) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem8033642 A M N x t s h1 h2 h3) (fun h4 : False => @lem8033278 A N t x h2)). Qed.
Lemma lem8033644 {A M N : Type'} (x : cart A N) (t : type24 A N) (s : type24 A M) (h1 : term436 A M N x s t) (h2 : t x) (h3 : term220 A M N t s) : False.
Proof. exact (EQ_MP (@lem8033643 A M N x t s h1 h2 h3) (@lem8033278 A N t x h2)). Qed.
Lemma lem8033645 {A M N : Type'} (x : cart A N) (t : type24 A N) (s : type24 A M) (h1 : term436 A M N x s t) (h2 : t x) (h3 : term220 A M N t s) : (term436 A M N x s t) = False.
Proof. exact (prop_ext (fun h4 : term436 A M N x s t => @lem8033644 A M N x t s h1 h2 h3) (fun h4 : False => @lem8033168 A M N x s t h1)). Qed.
Lemma lem8033646 {A M N : Type'} (x : cart A N) (t : type24 A N) (s : type24 A M) (h1 : term436 A M N x s t) (h2 : t x) (h3 : term220 A M N t s) : False.
Proof. exact (EQ_MP (@lem8033645 A M N x t s h1 h2 h3) (@lem8033168 A M N x s t h1)). Qed.
Lemma lem8033647 {A M N : Type'} (x : cart A N) (t : type24 A N) (s : type24 A M) (h1 : t x) (h2 : term220 A M N t s) : term435 A M N x s t.
Proof. exact (fun h0 : term436 A M N x s t => @lem8033646 A M N x t s h0 h1 h2). Qed.
Lemma lem8033648 {A M N : Type'} (x : cart A N) (t : type24 A N) (s : type24 A M) (h1 : t x) (h2 : term220 A M N t s) : term416 A M N x s t.
Proof. exact (EQ_MP (@lem8033167 A M N x s t) (@lem8033647 A M N x t s h1 h2)). Qed.
Lemma lem8033649 {A M N : Type'} (x : cart A N) (t : type24 A N) (s : type24 A M) (h1 : term220 A M N t s) : term417 A M N x s t.
Proof. exact (fun h0 : t x => @lem8033648 A M N x t s h0 h1). Qed.
Lemma lem8033654 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : term220 A M N t s) : term419 A M N s t.
Proof. exact (fun x : cart A N => @lem8033649 A M N x t s h1). Qed.
Lemma lem8033655 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term420 A M N s t.
Proof. exact (fun h0 : term220 A M N t s => @lem8033654 A M N t s h0). Qed.
Lemma lem8033660 {A M N : Type'} (t : type24 A N) : term430 A M N t.
Proof. exact (fun s : type24 A M => @lem8033655 A M N s t). Qed.
Lemma lem8033665 {A M N : Type'} : term434 A M N.
Proof. exact (fun t : type24 A N => @lem8033660 A M N t). Qed.
Lemma lem8033666 {A M N : Type'} : term433 A M N.
Proof. exact (EQ_MP (@lem8033161 A M N) (@lem8033665 A M N)). Qed.
Lemma lem8033667 {A M N : Type'} (t : type24 A N) : term468 A M N t.
Proof. exact (@lem8033666 A M N t). Qed.
Lemma lem8033668 {A M N : Type'} (t : type24 A N) : (term468 A M N t) = (term429 A M N t).
Proof. exact (eq_refl (term468 A M N t)). Qed.
Lemma lem8033669 {A M N : Type'} (t : type24 A N) : term429 A M N t.
Proof. exact (EQ_MP (@lem8033668 A M N t) (@lem8033667 A M N t)). Qed.
Lemma lem8033670 {A M N : Type'} (t : type24 A N) (s : type24 A M) : term469 A M N t s.
Proof. exact (@lem8033669 A M N t s). Qed.
Lemma lem8033671 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term469 A M N t s) = (term421 A M N s t).
Proof. exact (eq_refl (term469 A M N t s)). Qed.
Lemma lem8033672 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term421 A M N s t.
Proof. exact (EQ_MP (@lem8033671 A M N s t) (@lem8033670 A M N t s)). Qed.
Lemma lem8033674 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term421 A M N s t.
Proof. exact (@lem8032940 A M N s t (@lem8033672 A M N s t)). Qed.
Lemma lem8033675 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term422 A M N s t) : False.
Proof. exact (@lem8033674 A M N s t (@lem8032924 A M N s t h1)). Qed.
Lemma lem8033676 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term422 A M N s t) : (term422 A M N s t) = False.
Proof. exact (prop_ext (fun h2 : term422 A M N s t => @lem8033675 A M N s t h1) (fun h2 : False => @lem8032924 A M N s t h1)). Qed.
Lemma lem8033677 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term422 A M N s t) : False.
Proof. exact (EQ_MP (@lem8033676 A M N s t h1) (@lem8032924 A M N s t h1)). Qed.
Lemma lem8033678 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term421 A M N s t.
Proof. exact (fun h0 : term422 A M N s t => @lem8033677 A M N s t h0). Qed.
Lemma lem8033679 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term420 A M N s t.
Proof. exact (EQ_MP (@lem8032923 A M N s t) (@lem8033678 A M N s t)). Qed.
Lemma lem8033680 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term411 A M N s t.
Proof. exact (EQ_MP (@lem8032919 A M N s t) (@lem8033679 A M N s t)). Qed.
Lemma lem8033681 {A M N : Type'} (s : type24 A M) (t : type24 A N) : term410 A M N s t.
Proof. exact (EQ_MP (@lem8032773 A M N s t) (@lem8033680 A M N s t)). Qed.
Lemma lem8033682 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) (h2 : term38 A M s) (h3 : term38 A N t) : term195 A M N s t.
Proof. exact (@lem8033681 A M N s t (@lem8032697 A M N s t h1 h2 h3)). Qed.
Lemma lem8033683 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) (h2 : term38 A M s) (h3 : term38 A N t) : term173 A M N s t.
Proof. exact (EQ_MP (@lem8031591 A M N s t) (@lem8033682 A M N s t h1 h2 h3)). Qed.
Lemma lem8033684 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) (h2 : term38 A M s) (h3 : term38 A N t) : term129 A M N s t.
Proof. exact (EQ_MP (@lem8031530 A M N s t) (@lem8032685 A M N s t h1 h2 h3)). Qed.
Lemma lem8033685 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) (h2 : term38 A M s) (h3 : term38 A N t) : term174 A M N s t.
Proof. exact (EQ_MP (@lem8031467 A M N s t h1) (@lem8033683 A M N s t h1 h2 h3)). Qed.
Lemma lem8033686 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) (h2 : term38 A M s) (h3 : term38 A N t) : term130 A M N s t.
Proof. exact (EQ_MP (@lem8031084 A M N s t h1) (@lem8033684 A M N s t h1 h2 h3)). Qed.
Lemma lem8033687 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) (h2 : term38 A M s) (h3 : term38 A N t) : term470 A N t.
Proof. exact (ex_intro (term471 A N t) (term138 A M N s t) (@lem8033685 A M N s t h1 h2 h3)). Qed.
Lemma lem8033688 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) (h2 : term38 A M s) (h3 : term38 A N t) : term470 A M s.
Proof. exact (ex_intro (term471 A M s) (term92 A M N s t) (@lem8033686 A M N s t h1 h2 h3)). Qed.
Lemma lem8033689 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) (h2 : term38 A M s) (h3 : term38 A N t) : @FINITE (cart A N) t.
Proof. exact (@lem8030701 A N t (@lem8033687 A M N s t h1 h2 h3)). Qed.
Lemma lem8033690 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) (h2 : term38 A M s) (h3 : term38 A N t) : @FINITE (cart A M) s.
Proof. exact (@lem8030697 A M s (@lem8033688 A M N s t h1 h2 h3)). Qed.
Lemma lem8033691 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) (h2 : term38 A M s) (h3 : term38 A N t) : term34 A M N s t.
Proof. exact (conj (@lem8033690 A M N s t h1 h2 h3) (@lem8033689 A M N s t h1 h2 h3)). Qed.
Lemma lem8033692 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) (h2 : term38 A M s) (h3 : term38 A N t) : (term35 A M N s t) = (term34 A M N s t).
Proof. exact (prop_ext (fun h4 : term35 A M N s t => @lem8033691 A M N s t h1 h2 h3) (fun h4 : term34 A M N s t => @lem8030694 A M N s t h1)). Qed.
Lemma lem8033693 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term35 A M N s t) (h2 : term38 A M s) (h3 : term38 A N t) : term34 A M N s t.
Proof. exact (EQ_MP (@lem8033692 A M N s t h1 h2 h3) (@lem8030694 A M N s t h1)). Qed.
Lemma lem8033695 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A M s) (h2 : term38 A N t) : term472 A M N s t.
Proof. exact (fun h0 : term35 A M N s t => @lem8033693 A M N s t h0 h1 h2). Qed.
Lemma lem8033696 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A M s) (h2 : term38 A N t) : term473 A M N s t.
Proof. exact (conj (@lem8033695 A M N s t h1 h2) (@lem8030693 A M N s t)). Qed.
Lemma lem8033697 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term473 A M N s t) = ((term35 A M N s t) = (term34 A M N s t)).
Proof. exact (@lem32 (term35 A M N s t) (term34 A M N s t)). Qed.
Lemma lem8033698 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A M s) (h2 : term38 A N t) : (term35 A M N s t) = (term34 A M N s t).
Proof. exact (EQ_MP (@lem8033697 A M N s t) (@lem8033696 A M N s t h1 h2)). Qed.
Lemma lem8033699 {A M N : Type'} (s : type24 A M) (t : type24 A N) (h1 : term38 A M s) (h2 : term38 A N t) : (term35 A M N s t) = (term45 A M N s t).
Proof. exact (EQ_MP (@lem8030597 A M N s t h1 h2) (@lem8033698 A M N s t h1 h2)). Qed.
Lemma lem8033700 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : term38 A M s) : (term35 A M N s t) = (term45 A M N s t).
Proof. exact (or_elim (@lem8030217 A N t) (fun h0 : t = (@EMPTY (cart A N)) => @lem8030525 A M N s t h1 h0) (fun h0 : term38 A N t => @lem8033699 A M N s t h1 h0)). Qed.
Lemma lem8033701 {A M N : Type'} (t : type24 A N) (s : type24 A M) (h1 : s = (@EMPTY (cart A M))) : (term35 A M N s t) = (term45 A M N s t).
Proof. exact (or_elim (@lem8030217 A N t) (fun h0 : t = (@EMPTY (cart A N)) => @lem8030327 A M N s t h1 h0) (fun h0 : term38 A N t => @lem8030428 A M N t s h0 h1)). Qed.
Lemma lem8033702 {A M N : Type'} (s : type24 A M) (t : type24 A N) : (term35 A M N s t) = (term45 A M N s t).
Proof. exact (or_elim (@lem8030212 A M s) (fun h0 : s = (@EMPTY (cart A M)) => @lem8033701 A M N t s h0) (fun h0 : term38 A M s => @lem8033700 A M N t s h0)). Qed.
Lemma lem8033707 {A M N : Type'} (s : type24 A M) : term474 A M N s.
Proof. exact (fun t : type24 A N => @lem8033702 A M N s t). Qed.
Lemma lem8033712 {A M N : Type'} : term475 A M N.
Proof. exact (fun s : type24 A M => @lem8033707 A M N s). Qed.
