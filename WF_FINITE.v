Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_FINITE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_INSERT_spec.
Require Import FINITE_SUBSET_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import INFINITE_spec.
Require Import INFINITE_IMAGE_INJ_spec.
Require Import IN_INSERT_spec.
Require Import IN_UNIV_spec.
Require Import LT_0_spec.
Require Import LT_CASES_spec.
Require Import SUBSET_spec.
Require Import TRANSITIVE_STEPWISE_LT_spec.
Require Import num_INFINITE_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm129_spec.
Require Import thm137_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm310219_spec.
Require Import thm316636_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem5103134 {_83095 : Type'} : term0 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5103135 {_83095 : Type'} (p : _83095 -> Prop) : term1 _83095 p.
Proof. exact (@lem5103134 _83095 p). Qed.
Lemma lem5103136 {_83095 : Type'} (p : _83095 -> Prop) : (term1 _83095 p) = (term2 _83095 p).
Proof. exact (eq_refl (term1 _83095 p)). Qed.
Lemma lem5103137 {_83095 : Type'} (p : _83095 -> Prop) : term2 _83095 p.
Proof. exact (EQ_MP (@lem5103136 _83095 p) (@lem5103135 _83095 p)). Qed.
Lemma lem5103138 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term3 _83095 p x.
Proof. exact (@lem5103137 _83095 p x). Qed.
Lemma lem5103139 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = ((term4 _83095 x p) = (p x)).
Proof. exact (eq_refl (term3 _83095 p x)). Qed.
Lemma lem5103148 {A : Type'} (x : A) : term5 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5103149 {A : Type'} (x : A) : (term5 A x) = (term6 A x).
Proof. exact (eq_refl (term5 A x)). Qed.
Lemma lem5103150 {A : Type'} (x : A) : term6 A x.
Proof. exact (EQ_MP (@lem5103149 A x) (@lem5103148 A x)). Qed.
Lemma lem5103151 {A : Type'} (x : A) (y : A) : term7 A x y.
Proof. exact (@lem5103150 A x y). Qed.
Lemma lem5103152 {A : Type'} (y : A) (x : A) : (term7 A x y) = (term8 A y x).
Proof. exact (eq_refl (term7 A x y)). Qed.
Lemma lem5103153 {A : Type'} (y : A) (x : A) : term8 A y x.
Proof. exact (EQ_MP (@lem5103152 A y x) (@lem5103151 A x y)). Qed.
Lemma lem5103154 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term9 A y x s.
Proof. exact (@lem5103153 A y x s). Qed.
Lemma lem5103155 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term9 A y x s) = ((term10 A x y s) = (term11 A y x s)).
Proof. exact (eq_refl (term9 A y x s)). Qed.
Lemma lem5103157 {A : Type'} (x : A) : term12 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem5103158 {A : Type'} (x : A) : (term12 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term12 A x)). Qed.
Lemma lem5103159 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem5103158 A x) (@lem5103157 A x)). Qed.
Lemma lem5103160 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem5103162 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term13 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem5103163 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term13 _87967 _87968 P f) = (term14 _87967 _87968 P f).
Proof. exact (eq_refl (term13 _87967 _87968 P f)). Qed.
Lemma lem5103164 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term14 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem5103163 _87967 _87968 P f) (@lem5103162 _87967 _87968 P f)). Qed.
Lemma lem5103165 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term15 _87967 _87968 P f s.
Proof. exact (@lem5103164 _87967 _87968 P f s). Qed.
Lemma lem5103166 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term15 _87967 _87968 P f s) = ((term16 _87967 _87968 f s P) = (term17 _87967 _87968 s P f)).
Proof. exact (eq_refl (term15 _87967 _87968 P f s)). Qed.
Lemma lem5103168 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem5103169 {A : Type'} (s : A -> Prop) : (term18 A s) = (term19 A s).
Proof. exact (eq_refl (term18 A s)). Qed.
Lemma lem5103170 {A : Type'} (s : A -> Prop) : term19 A s.
Proof. exact (EQ_MP (@lem5103169 A s) (@lem5103168 A s)). Qed.
Lemma lem5103171 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term20 A s t.
Proof. exact (@lem5103170 A s t). Qed.
Lemma lem5103172 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term20 A s t) = ((@SUBSET A s t) = (term21 A s t)).
Proof. exact (eq_refl (term20 A s t)). Qed.
Lemma lem5103174 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (h1). Qed.
Lemma lem5103175 {A : Type'} (s : A -> Prop) (h1 : term22 A) : term23 A s.
Proof. exact (@lem5103174 A h1 s). Qed.
Lemma lem5103176 {A : Type'} (s : A -> Prop) : (term23 A s) = (term24 A s).
Proof. exact (eq_refl (term23 A s)). Qed.
Lemma lem5103177 {A : Type'} (s : A -> Prop) (h1 : term22 A) : term24 A s.
Proof. exact (EQ_MP (@lem5103176 A s) (@lem5103175 A s h1)). Qed.
Lemma lem5103178 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term22 A) : term25 A s t.
Proof. exact (@lem5103177 A s h1 t). Qed.
Lemma lem5103179 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term25 A s t) = (term26 A t s).
Proof. exact (eq_refl (term25 A s t)). Qed.
Lemma lem5103180 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term22 A) : term26 A t s.
Proof. exact (EQ_MP (@lem5103179 A t s) (@lem5103178 A s t h1)). Qed.
Lemma lem5103181 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term27 A s t) : term27 A s t.
Proof. exact (h1). Qed.
Lemma lem5103182 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term22 A) (h2 : term27 A s t) : @FINITE A s.
Proof. exact (@lem5103180 A t s h1 (@lem5103181 A s t h2)). Qed.
Lemma lem5103183 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term27 A s t) : term28 A s.
Proof. exact (fun h0 : term22 A => @lem5103182 A s t h0 h1). Qed.
Lemma lem5103184 {A : Type'} (s : A -> Prop) (h1 : term29 A s) : term29 A s.
Proof. exact (h1). Qed.
Lemma lem5103185 {A : Type'} (s : A -> Prop) (h1 : term29 A s) : term28 A s.
Proof. exact (ex_elim (@lem5103184 A s h1) (fun t : A -> Prop => fun h0 : term30 A s t => @lem5103183 A s t h0)). Qed.
Lemma lem5103186 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (h1). Qed.
Lemma lem5103187 {A : Type'} (s : A -> Prop) (h1 : term22 A) (h2 : term29 A s) : @FINITE A s.
Proof. exact (@lem5103185 A s h2 (@lem5103186 A h1)). Qed.
Lemma lem5103188 {A : Type'} (s : A -> Prop) (h1 : term22 A) : term31 A s.
Proof. exact (fun h0 : term29 A s => @lem5103187 A s h1 h0). Qed.
Lemma lem5103189 {A : Type'} (h1 : term22 A) : term32 A.
Proof. exact (fun s : A -> Prop => @lem5103188 A s h1). Qed.
Lemma lem5103190 {A : Type'} : term33 A.
Proof. exact (fun h0 : term22 A => @lem5103189 A h0). Qed.
Lemma lem5103191 {A : Type'} : term32 A.
Proof. exact (@lem5103190 A (@lem3599924 A)). Qed.
Lemma lem5103192 {A : Type'} (s : A -> Prop) : term34 A s.
Proof. exact (@lem5103191 A s). Qed.
Lemma lem5103193 {A : Type'} (s : A -> Prop) : (term34 A s) = (term31 A s).
Proof. exact (eq_refl (term34 A s)). Qed.
Lemma lem5103195 {A : Type'} (s : A -> Prop) : term35 A s.
Proof. exact (@lem3198543 A s). Qed.
Lemma lem5103196 {A : Type'} (s : A -> Prop) : (term35 A s) = ((@INFINITE A s) = (term36 A s)).
Proof. exact (eq_refl (term35 A s)). Qed.
Lemma lem5103198 : (@INFINITE nat (@UNIV nat)) = ((@INFINITE nat (@UNIV nat)) = True).
Proof. exact (@lem7 (@INFINITE nat (@UNIV nat))). Qed.
Lemma lem5103210 {A : Type'} : term37 A.
Proof. exact (@lem3630638 nat A). Qed.
Lemma lem5103211 {A : Type'} (s : nat -> A) : term38 A s.
Proof. exact (@lem5103210 A s). Qed.
Lemma lem5103212 {A : Type'} (s : nat -> A) : (term38 A s) = (term39 A s).
Proof. exact (eq_refl (term38 A s)). Qed.
Lemma lem5103213 {A : Type'} (s : nat -> A) : term39 A s.
Proof. exact (EQ_MP (@lem5103212 A s) (@lem5103211 A s)). Qed.
Lemma lem5103214 (t1 : Prop) : term40 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5103215 (t1 : Prop) : (term40 t1) = (term41 t1).
Proof. exact (eq_refl (term40 t1)). Qed.
Lemma lem5103216 (t1 : Prop) : term41 t1.
Proof. exact (EQ_MP (@lem5103215 t1) (@lem5103214 t1)). Qed.
Lemma lem5103217 (t1 : Prop) (t2 : Prop) : term42 t1 t2.
Proof. exact (@lem5103216 t1 t2). Qed.
Lemma lem5103218 (t1 : Prop) (t2 : Prop) : (term42 t1 t2) = (term43 t1 t2).
Proof. exact (eq_refl (term42 t1 t2)). Qed.
Lemma lem5103219 (t1 : Prop) (t2 : Prop) : term43 t1 t2.
Proof. exact (EQ_MP (@lem5103218 t1 t2) (@lem5103217 t1 t2)). Qed.
Lemma lem5103220 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term44 t1 t2 t3.
Proof. exact (@lem5103219 t1 t2 t3). Qed.
Lemma lem5103221 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term44 t1 t2 t3) = ((term45 t1 t2 t3) = (term46 t1 t2 t3)).
Proof. exact (eq_refl (term44 t1 t2 t3)). Qed.
Lemma lem5103222 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term45 t1 t2 t3) = (term46 t1 t2 t3).
Proof. exact (EQ_MP (@lem5103221 t1 t2 t3) (@lem5103220 t1 t2 t3)). Qed.
Lemma lem5103223 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term46 t1 t2 t3) = (term45 t1 t2 t3).
Proof. exact (SYM (@lem5103222 t1 t2 t3)). Qed.
Lemma lem5103224 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem5103225 (R : type1605) (h1 : term47) : term48 R.
Proof. exact (@lem5103224 h1 R). Qed.
Lemma lem5103226 (R : type1605) : (term48 R) = (term49 R).
Proof. exact (eq_refl (term48 R)). Qed.
Lemma lem5103227 (R : type1605) (h1 : term47) : term49 R.
Proof. exact (EQ_MP (@lem5103226 R) (@lem5103225 R h1)). Qed.
Lemma lem5103228 (R : type1605) (h1 : term50 R) : term50 R.
Proof. exact (h1). Qed.
Lemma lem5103229 (R : type1605) (h1 : term47) (h2 : term50 R) : term51 R.
Proof. exact (@lem5103227 R h1 (@lem5103228 R h2)). Qed.
Lemma lem5103230 (R : type1605) (h1 : term50 R) : term52 R.
Proof. exact (fun h0 : term47 => @lem5103229 R h0 h1). Qed.
Lemma lem5103231 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem5103232 (R : type1605) (h1 : term47) (h2 : term50 R) : term51 R.
Proof. exact (@lem5103230 R h2 (@lem5103231 h1)). Qed.
Lemma lem5103233 (R : type1605) (h1 : term47) : term49 R.
Proof. exact (fun h0 : term50 R => @lem5103232 R h1 h0). Qed.
Lemma lem5103234 (h1 : term47) : term47.
Proof. exact (fun R : type1605 => @lem5103233 R h1). Qed.
Lemma lem5103235 : term53.
Proof. exact (fun h0 : term47 => @lem5103234 h0). Qed.
Lemma lem5103236 : term47.
Proof. exact (@lem5103235 (@lem286705)). Qed.
Lemma lem5103237 (R : type1605) : term48 R.
Proof. exact (@lem5103236 R). Qed.
Lemma lem5103238 (R : type1605) : (term48 R) = (term49 R).
Proof. exact (eq_refl (term48 R)). Qed.
Lemma lem5103240 {A : Type'} (lt2 : type1402 A) (h1 : term54 A lt2) : term54 A lt2.
Proof. exact (h1). Qed.
Lemma lem5103241 {A : Type'} (lt2 : type1402 A) (h1 : term55 A lt2) : term55 A lt2.
Proof. exact (h1). Qed.
Lemma lem5103242 {A : Type'} (lt2 : type1402 A) (h1 : term56 A lt2) : term56 A lt2.
Proof. exact (h1). Qed.
Lemma lem5103243 {A : Type'} (lt2 : type1402 A) (h1 : term57 A lt2) : term57 A lt2.
Proof. exact (h1). Qed.
Lemma lem5103244 {A : Type'} (lt2 : type1402 A) (h1 : term58 A lt2) : term58 A lt2.
Proof. exact (h1). Qed.
Lemma lem5103246 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term59 A lt2).
Proof. exact (EQ_MP (@lem310219 A lt2) (@lem316636 A lt2)). Qed.
Lemma lem5103247 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term59 A lt2).
Proof. exact (@lem5103246 A lt2). Qed.
Lemma lem5103256 {A : Type'} (lt2 : type1402 A) : (term59 A lt2) = (@WF A lt2).
Proof. exact (SYM (@lem5103247 A lt2)). Qed.
Lemma lem5103257 {A : Type'} (lt2 : type1402 A) (h1 : term60 A lt2) : term60 A lt2.
Proof. exact (h1). Qed.
Lemma lem5103258 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term61 A lt2 s) : term61 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem5103259 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term62 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem5103261 (R : type1605) : term49 R.
Proof. exact (EQ_MP (@lem5103238 R) (@lem5103237 R)). Qed.
Lemma lem5103262 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term63 A lt2 s.
Proof. exact (@lem5103261 (term64 A lt2 s)). Qed.
Lemma lem5103263 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term65 A lt2 s x) = (term66 A lt2 s x).
Proof. exact (eq_refl (term65 A lt2 s x)). Qed.
Lemma lem5103264 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5103265 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) : (term67 A lt2 s x y) = (term68 A lt2 s x y).
Proof. exact (MK_COMB (@lem5103263 A lt2 s x) (@lem5103264 y)). Qed.
Lemma lem5103266 {A : Type'} (lt2 : type1402 A) (y : nat) (s : nat -> A) (x : nat) : (term68 A lt2 s x y) = (term69 A lt2 y s x).
Proof. exact (eq_refl (term68 A lt2 s x y)). Qed.
Lemma lem5103267 {A : Type'} (lt2 : type1402 A) (y : nat) (s : nat -> A) (x : nat) : (term67 A lt2 s x y) = (term69 A lt2 y s x).
Proof. exact (TRANS (@lem5103265 A lt2 s x y) (@lem5103266 A lt2 y s x)). Qed.
Lemma lem5103268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5103269 {A : Type'} (lt2 : type1402 A) (y : nat) (s : nat -> A) (x : nat) : (term70 A lt2 s x y) = (term71 A lt2 y s x).
Proof. exact (MK_COMB (@lem5103268) (@lem5103267 A lt2 y s x)). Qed.
Lemma lem5103270 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (y : nat) : (term65 A lt2 s y) = (term66 A lt2 s y).
Proof. exact (eq_refl (term65 A lt2 s y)). Qed.
Lemma lem5103271 (z : nat) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5103272 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (y : nat) (z : nat) : (term67 A lt2 s y z) = (term68 A lt2 s y z).
Proof. exact (MK_COMB (@lem5103270 A lt2 s y) (@lem5103271 z)). Qed.
Lemma lem5103273 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term68 A lt2 s y z) = (term69 A lt2 z s y).
Proof. exact (eq_refl (term68 A lt2 s y z)). Qed.
Lemma lem5103274 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term67 A lt2 s y z) = (term69 A lt2 z s y).
Proof. exact (TRANS (@lem5103272 A lt2 s y z) (@lem5103273 A lt2 z s y)). Qed.
Lemma lem5103275 {A : Type'} (x : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term72 A x lt2 s y z) = (term73 A x lt2 z s y).
Proof. exact (MK_COMB (@lem5103269 A lt2 y s x) (@lem5103274 A lt2 z s y)). Qed.
Lemma lem5103276 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5103277 {A : Type'} (x : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term74 A x lt2 s y z) = (term75 A x lt2 z s y).
Proof. exact (MK_COMB (@lem5103276) (@lem5103275 A x lt2 z s y)). Qed.
Lemma lem5103278 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term65 A lt2 s x) = (term66 A lt2 s x).
Proof. exact (eq_refl (term65 A lt2 s x)). Qed.
Lemma lem5103279 (z : nat) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5103280 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (z : nat) : (term67 A lt2 s x z) = (term68 A lt2 s x z).
Proof. exact (MK_COMB (@lem5103278 A lt2 s x) (@lem5103279 z)). Qed.
Lemma lem5103281 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term68 A lt2 s x z) = (term69 A lt2 z s x).
Proof. exact (eq_refl (term68 A lt2 s x z)). Qed.
Lemma lem5103282 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term67 A lt2 s x z) = (term69 A lt2 z s x).
Proof. exact (TRANS (@lem5103280 A lt2 s x z) (@lem5103281 A lt2 z s x)). Qed.
Lemma lem5103283 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term76 A y lt2 s x z) = (term77 A y lt2 z s x).
Proof. exact (MK_COMB (@lem5103277 A x lt2 z s y) (@lem5103282 A lt2 z s x)). Qed.
Lemma lem5103284 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term78 A y lt2 s x) = (term79 A y lt2 s x).
Proof. exact (fun_ext (fun z : nat => @lem5103283 A y lt2 z s x)). Qed.
Lemma lem5103285 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5103286 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term80 A y lt2 s x) = (term81 A y lt2 s x).
Proof. exact (MK_COMB (@lem5103285) (@lem5103284 A y lt2 s x)). Qed.
Lemma lem5103287 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term82 A lt2 s x) = (term83 A lt2 s x).
Proof. exact (fun_ext (fun y : nat => @lem5103286 A y lt2 s x)). Qed.
Lemma lem5103288 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5103289 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term84 A lt2 s x) = (term85 A lt2 s x).
Proof. exact (MK_COMB (@lem5103288) (@lem5103287 A lt2 s x)). Qed.
Lemma lem5103290 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term86 A lt2 s) = (term87 A lt2 s).
Proof. exact (fun_ext (fun x : nat => @lem5103289 A lt2 s x)). Qed.
Lemma lem5103291 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5103292 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term88 A lt2 s) = (term89 A lt2 s).
Proof. exact (MK_COMB (@lem5103291) (@lem5103290 A lt2 s)). Qed.
Lemma lem5103293 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5103294 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term90 A lt2 s) = (term91 A lt2 s).
Proof. exact (MK_COMB (@lem5103293) (@lem5103292 A lt2 s)). Qed.
Lemma lem5103295 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term65 A lt2 s n) = (term66 A lt2 s n).
Proof. exact (eq_refl (term65 A lt2 s n)). Qed.
Lemma lem5103296 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem5103297 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term92 A lt2 s n) = (term93 A lt2 s n).
Proof. exact (MK_COMB (@lem5103295 A lt2 s n) (@lem5103296 n)). Qed.
Lemma lem5103298 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term93 A lt2 s n) = (term94 A lt2 s n).
Proof. exact (eq_refl (term93 A lt2 s n)). Qed.
Lemma lem5103299 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term92 A lt2 s n) = (term94 A lt2 s n).
Proof. exact (TRANS (@lem5103297 A lt2 s n) (@lem5103298 A lt2 s n)). Qed.
Lemma lem5103300 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term95 A lt2 s) = (term96 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5103299 A lt2 s n)). Qed.
Lemma lem5103301 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5103302 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term97 A lt2 s) = (term61 A lt2 s).
Proof. exact (MK_COMB (@lem5103301) (@lem5103300 A lt2 s)). Qed.
Lemma lem5103303 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term98 A lt2 s) = (term99 A lt2 s).
Proof. exact (MK_COMB (@lem5103294 A lt2 s) (@lem5103302 A lt2 s)). Qed.
Lemma lem5103304 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5103305 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term100 A lt2 s) = (term101 A lt2 s).
Proof. exact (MK_COMB (@lem5103304) (@lem5103303 A lt2 s)). Qed.
Lemma lem5103306 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term65 A lt2 s m) = (term66 A lt2 s m).
Proof. exact (eq_refl (term65 A lt2 s m)). Qed.
Lemma lem5103307 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem5103308 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) (n : nat) : (term67 A lt2 s m n) = (term68 A lt2 s m n).
Proof. exact (MK_COMB (@lem5103306 A lt2 s m) (@lem5103307 n)). Qed.
Lemma lem5103309 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term68 A lt2 s m n) = (term69 A lt2 n s m).
Proof. exact (eq_refl (term68 A lt2 s m n)). Qed.
Lemma lem5103310 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term67 A lt2 s m n) = (term69 A lt2 n s m).
Proof. exact (TRANS (@lem5103308 A lt2 s m n) (@lem5103309 A lt2 n s m)). Qed.
Lemma lem5103311 (m : nat) (n : nat) : (term102 m n) = (term102 m n).
Proof. exact (eq_refl (term102 m n)). Qed.
Lemma lem5103312 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term103 A lt2 s m n) = (term104 A lt2 n s m).
Proof. exact (MK_COMB (@lem5103311 m n) (@lem5103310 A lt2 n s m)). Qed.
Lemma lem5103313 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term105 A lt2 s m) = (term106 A lt2 s m).
Proof. exact (fun_ext (fun n : nat => @lem5103312 A lt2 n s m)). Qed.
Lemma lem5103314 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5103315 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term107 A lt2 s m) = (term108 A lt2 s m).
Proof. exact (MK_COMB (@lem5103314) (@lem5103313 A lt2 s m)). Qed.
Lemma lem5103316 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term109 A lt2 s) = (term110 A lt2 s).
Proof. exact (fun_ext (fun m : nat => @lem5103315 A lt2 s m)). Qed.
Lemma lem5103317 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5103318 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term111 A lt2 s) = (term62 A lt2 s).
Proof. exact (MK_COMB (@lem5103317) (@lem5103316 A lt2 s)). Qed.
Lemma lem5103319 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term63 A lt2 s) = (term112 A lt2 s).
Proof. exact (MK_COMB (@lem5103305 A lt2 s) (@lem5103318 A lt2 s)). Qed.
Lemma lem5103320 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term112 A lt2 s.
Proof. exact (EQ_MP (@lem5103319 A lt2 s) (@lem5103262 A lt2 s)). Qed.
Lemma lem5103322 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5103323 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term99 A lt2 s) = (term114 A lt2 s).
Proof. exact (@lem5103322 (term99 A lt2 s)). Qed.
Lemma lem5103324 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term114 A lt2 s) = (term99 A lt2 s).
Proof. exact (SYM (@lem5103323 A lt2 s)). Qed.
Lemma lem5103325 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term115 A lt2 s) : term115 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem5103328 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term116 A lt2 s) : term116 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem5103329 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term117 A lt2 s.
Proof. exact (fun h0 : term116 A lt2 s => @lem5103328 A lt2 s h0). Qed.
Lemma lem5103330 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term117 A lt2 s) : term117 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem5103331 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term116 A lt2 s) : term116 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem5103332 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term116 A lt2 s) (h2 : term117 A lt2 s) : term116 A lt2 s.
Proof. exact (@lem5103330 A lt2 s h2 (@lem5103331 A lt2 s h1)). Qed.
Lemma lem5103333 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term116 A lt2 s) : term118 A lt2 s.
Proof. exact (fun h0 : term117 A lt2 s => @lem5103332 A lt2 s h1 h0). Qed.
Lemma lem5103334 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term117 A lt2 s) : term117 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem5103335 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term116 A lt2 s) (h2 : term117 A lt2 s) : term116 A lt2 s.
Proof. exact (@lem5103333 A lt2 s h1 (@lem5103334 A lt2 s h2)). Qed.
Lemma lem5103336 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term117 A lt2 s) : term117 A lt2 s.
Proof. exact (fun h0 : term116 A lt2 s => @lem5103335 A lt2 s h0 h1). Qed.
Lemma lem5103337 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term119 A lt2 s.
Proof. exact (fun h0 : term117 A lt2 s => @lem5103336 A lt2 s h0). Qed.
Lemma lem5103340 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term117 A lt2 s.
Proof. exact (@lem5103337 A lt2 s (@lem5103329 A lt2 s)). Qed.
Lemma lem5103341 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term117 A lt2 s.
Proof. exact (@lem5103340 A lt2 s). Qed.
Lemma lem5103391 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5103392 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term114 A lt2 s) = (term120 A lt2 s).
Proof. exact (@lem5103391 (term115 A lt2 s)). Qed.
Lemma lem5103394 (t : Prop) : (term121 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5103395 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term120 A lt2 s) = (term99 A lt2 s).
Proof. exact (@lem5103394 (term99 A lt2 s)). Qed.
Lemma lem5103398 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term114 A lt2 s) = (term99 A lt2 s).
Proof. exact (TRANS (@lem5103392 A lt2 s) (@lem5103395 A lt2 s)). Qed.
Lemma lem5103419 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term122 A lt2 s) = (term122 A lt2 s).
Proof. exact (eq_refl (term122 A lt2 s)). Qed.
Lemma lem5103420 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term123 A lt2 s) = (term124 A lt2 s).
Proof. exact (MK_COMB (@lem5103419 A lt2 s) (@lem5103398 A lt2 s)). Qed.
Lemma lem5103423 {A : Type'} (lt2 : type1402 A) : (term125 A lt2) = (term125 A lt2).
Proof. exact (eq_refl (term125 A lt2)). Qed.
Lemma lem5103424 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term126 A lt2 s) = (term127 A lt2 s).
Proof. exact (MK_COMB (@lem5103423 A lt2) (@lem5103420 A lt2 s)). Qed.
Lemma lem5103427 {A : Type'} (lt2 : type1402 A) : (term128 A lt2) = (term128 A lt2).
Proof. exact (eq_refl (term128 A lt2)). Qed.
Lemma lem5103428 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term129 A lt2 s) = (term130 A lt2 s).
Proof. exact (MK_COMB (@lem5103427 A lt2) (@lem5103424 A lt2 s)). Qed.
Lemma lem5103431 {A : Type'} (lt2 : type1402 A) : (term131 A lt2) = (term131 A lt2).
Proof. exact (eq_refl (term131 A lt2)). Qed.
Lemma lem5103432 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term116 A lt2 s) = (term132 A lt2 s).
Proof. exact (MK_COMB (@lem5103431 A lt2) (@lem5103428 A lt2 s)). Qed.
Lemma lem5103435 {A : Type'} (s : nat -> A) : (term133 A s) = (term134 A s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5103432 A lt2 s)). Qed.
Lemma lem5103436 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5103437 {A : Type'} (s : nat -> A) : (term135 A s) = (term136 A s).
Proof. exact (MK_COMB (@lem5103436 A) (@lem5103435 A s)). Qed.
Lemma lem5103442 {A : Type'} : (term137 A) = (term138 A).
Proof. exact (fun_ext (fun s : nat -> A => @lem5103437 A s)). Qed.
Lemma lem5103443 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5103450 {A : Type'} : (term139 A) = (term140 A).
Proof. exact (MK_COMB (@lem5103443 A) (@lem5103442 A)). Qed.
Lemma lem5103451 {A : Type'} (_66533 : type418 A) (h1 : _66533 = (term141 A)) : _66533 = (term141 A).
Proof. exact (h1). Qed.
Lemma lem5103452 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem5103453 {A : Type'} (lt2 : type1402 A) (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (_66533 lt2) = (term142 A lt2).
Proof. exact (MK_COMB (@lem5103451 A _66533 h1) (@lem5103452 A lt2)). Qed.
Lemma lem5103454 {A : Type'} (lt2 : type1402 A) : (term142 A lt2) = (term143 A lt2).
Proof. exact (eq_refl (term142 A lt2)). Qed.
Lemma lem5103455 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term144 A _66533 lt2) = (term144 A _66533 lt2).
Proof. exact (eq_refl (term144 A _66533 lt2)). Qed.
Lemma lem5103456 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : ((_66533 lt2) = (term142 A lt2)) = ((_66533 lt2) = (term143 A lt2)).
Proof. exact (MK_COMB (@lem5103455 A _66533 lt2) (@lem5103454 A lt2)). Qed.
Lemma lem5103457 {A : Type'} (lt2 : type1402 A) (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (_66533 lt2) = (term143 A lt2).
Proof. exact (EQ_MP (@lem5103456 A _66533 lt2) (@lem5103453 A lt2 _66533 h1)). Qed.
Lemma lem5103458 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5103459 {A : Type'} (lt2 : type1402 A) (x : A) (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (_66533 lt2 x) = (term145 A lt2 x).
Proof. exact (MK_COMB (@lem5103457 A lt2 _66533 h1) (@lem5103458 A x)). Qed.
Lemma lem5103460 {A : Type'} (lt2 : type1402 A) (x : A) : (term145 A lt2 x) = (term146 A lt2 x).
Proof. exact (eq_refl (term145 A lt2 x)). Qed.
Lemma lem5103461 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term147 A _66533 lt2 x) = (term147 A _66533 lt2 x).
Proof. exact (eq_refl (term147 A _66533 lt2 x)). Qed.
Lemma lem5103462 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : ((_66533 lt2 x) = (term145 A lt2 x)) = ((_66533 lt2 x) = (term146 A lt2 x)).
Proof. exact (MK_COMB (@lem5103461 A _66533 lt2 x) (@lem5103460 A lt2 x)). Qed.
Lemma lem5103463 {A : Type'} (lt2 : type1402 A) (x : A) (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (_66533 lt2 x) = (term146 A lt2 x).
Proof. exact (EQ_MP (@lem5103462 A _66533 lt2 x) (@lem5103459 A lt2 x _66533 h1)). Qed.
Lemma lem5103475 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term94 A lt2 s n) = (term94 A lt2 s n).
Proof. exact (eq_refl (term94 A lt2 s n)). Qed.
Lemma lem5103476 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term96 A lt2 s) = (term96 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5103475 A lt2 s n)). Qed.
Lemma lem5103477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5103478 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term61 A lt2 s) = (term61 A lt2 s).
Proof. exact (MK_COMB (@lem5103477) (@lem5103476 A lt2 s)). Qed.
Lemma lem5103511 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term77 A y lt2 z s x) = (term77 A y lt2 z s x).
Proof. exact (eq_refl (term77 A y lt2 z s x)). Qed.
Lemma lem5103512 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term79 A y lt2 s x) = (term79 A y lt2 s x).
Proof. exact (fun_ext (fun z : nat => @lem5103511 A y lt2 z s x)). Qed.
Lemma lem5103513 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5103514 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term81 A y lt2 s x) = (term81 A y lt2 s x).
Proof. exact (MK_COMB (@lem5103513) (@lem5103512 A y lt2 s x)). Qed.
Lemma lem5103515 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term83 A lt2 s x) = (term83 A lt2 s x).
Proof. exact (fun_ext (fun y : nat => @lem5103514 A y lt2 s x)). Qed.
Lemma lem5103516 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5103517 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term85 A lt2 s x) = (term85 A lt2 s x).
Proof. exact (MK_COMB (@lem5103516) (@lem5103515 A lt2 s x)). Qed.
Lemma lem5103518 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term87 A lt2 s) = (term87 A lt2 s).
Proof. exact (fun_ext (fun x : nat => @lem5103517 A lt2 s x)). Qed.
Lemma lem5103519 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5103520 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term89 A lt2 s) = (term89 A lt2 s).
Proof. exact (MK_COMB (@lem5103519) (@lem5103518 A lt2 s)). Qed.
Lemma lem5103521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5103522 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term91 A lt2 s) = (term91 A lt2 s).
Proof. exact (MK_COMB (@lem5103521) (@lem5103520 A lt2 s)). Qed.
Lemma lem5103523 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term99 A lt2 s) = (term99 A lt2 s).
Proof. exact (MK_COMB (@lem5103522 A lt2 s) (@lem5103478 A lt2 s)). Qed.
Lemma lem5103534 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term94 A lt2 s n) = (term94 A lt2 s n).
Proof. exact (eq_refl (term94 A lt2 s n)). Qed.
Lemma lem5103535 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term96 A lt2 s) = (term96 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5103534 A lt2 s n)). Qed.
Lemma lem5103536 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5103537 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term61 A lt2 s) = (term61 A lt2 s).
Proof. exact (MK_COMB (@lem5103536) (@lem5103535 A lt2 s)). Qed.
Lemma lem5103538 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5103539 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term122 A lt2 s) = (term122 A lt2 s).
Proof. exact (MK_COMB (@lem5103538) (@lem5103537 A lt2 s)). Qed.
Lemma lem5103540 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term124 A lt2 s) = (term124 A lt2 s).
Proof. exact (MK_COMB (@lem5103539 A lt2 s) (@lem5103523 A lt2 s)). Qed.
Lemma lem5103542 {A : Type'} (lt2 : type1402 A) (x : A) (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (term146 A lt2 x) = (_66533 lt2 x).
Proof. exact (SYM (@lem5103463 A lt2 x _66533 h1)). Qed.
Lemma lem5103543 {A : Type'} (lt2 : type1402 A) (x : A) (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (term146 A lt2 x) = (_66533 lt2 x).
Proof. exact (@lem5103542 A lt2 x _66533 h1). Qed.
Lemma lem5103544 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5103545 {A : Type'} (lt2 : type1402 A) (x : A) (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (term148 A lt2 x) = (term149 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5103544 A) (@lem5103543 A lt2 x _66533 h1)). Qed.
Lemma lem5103546 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem5103547 {A : Type'} (lt2 : type1402 A) (x : A) (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (term150 A lt2 x) = (term151 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5103546 A) (@lem5103545 A lt2 x _66533 h1)). Qed.
Lemma lem5103548 {A : Type'} (lt2 : type1402 A) (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (term152 A lt2) = (term153 A _66533 lt2).
Proof. exact (fun_ext (fun x : A => @lem5103547 A lt2 x _66533 h1)). Qed.
Lemma lem5103549 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103550 {A : Type'} (lt2 : type1402 A) (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (term57 A lt2) = (term154 A _66533 lt2).
Proof. exact (MK_COMB (@lem5103549 A) (@lem5103548 A lt2 _66533 h1)). Qed.
Lemma lem5103551 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5103552 {A : Type'} (lt2 : type1402 A) (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (term125 A lt2) = (term155 A _66533 lt2).
Proof. exact (MK_COMB (@lem5103551) (@lem5103550 A lt2 _66533 h1)). Qed.
Lemma lem5103553 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (term127 A lt2 s) = (term156 A _66533 lt2 s).
Proof. exact (MK_COMB (@lem5103552 A lt2 _66533 h1) (@lem5103540 A lt2 s)). Qed.
Lemma lem5103574 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term157 A y lt2 x z) = (term157 A y lt2 x z).
Proof. exact (eq_refl (term157 A y lt2 x z)). Qed.
Lemma lem5103575 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term158 A y lt2 x) = (term158 A y lt2 x).
Proof. exact (fun_ext (fun z : A => @lem5103574 A y lt2 x z)). Qed.
Lemma lem5103576 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103577 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term159 A y lt2 x) = (term159 A y lt2 x).
Proof. exact (MK_COMB (@lem5103576 A) (@lem5103575 A y lt2 x)). Qed.
Lemma lem5103578 {A : Type'} (lt2 : type1402 A) (x : A) : (term160 A lt2 x) = (term160 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5103577 A y lt2 x)). Qed.
Lemma lem5103579 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103580 {A : Type'} (lt2 : type1402 A) (x : A) : (term161 A lt2 x) = (term161 A lt2 x).
Proof. exact (MK_COMB (@lem5103579 A) (@lem5103578 A lt2 x)). Qed.
Lemma lem5103581 {A : Type'} (lt2 : type1402 A) : (term162 A lt2) = (term162 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5103580 A lt2 x)). Qed.
Lemma lem5103582 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103583 {A : Type'} (lt2 : type1402 A) : (term58 A lt2) = (term58 A lt2).
Proof. exact (MK_COMB (@lem5103582 A) (@lem5103581 A lt2)). Qed.
Lemma lem5103584 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5103585 {A : Type'} (lt2 : type1402 A) : (term128 A lt2) = (term128 A lt2).
Proof. exact (MK_COMB (@lem5103584) (@lem5103583 A lt2)). Qed.
Lemma lem5103586 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (term130 A lt2 s) = (term163 A _66533 lt2 s).
Proof. exact (MK_COMB (@lem5103585 A lt2) (@lem5103553 A lt2 s _66533 h1)). Qed.
Lemma lem5103593 {A : Type'} (lt2 : type1402 A) (x : A) : (term164 A lt2 x) = (term164 A lt2 x).
Proof. exact (eq_refl (term164 A lt2 x)). Qed.
Lemma lem5103594 {A : Type'} (lt2 : type1402 A) : (term165 A lt2) = (term165 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5103593 A lt2 x)). Qed.
Lemma lem5103595 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103596 {A : Type'} (lt2 : type1402 A) : (term56 A lt2) = (term56 A lt2).
Proof. exact (MK_COMB (@lem5103595 A) (@lem5103594 A lt2)). Qed.
Lemma lem5103597 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5103598 {A : Type'} (lt2 : type1402 A) : (term131 A lt2) = (term131 A lt2).
Proof. exact (MK_COMB (@lem5103597) (@lem5103596 A lt2)). Qed.
Lemma lem5103599 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (term132 A lt2 s) = (term166 A _66533 lt2 s).
Proof. exact (MK_COMB (@lem5103598 A lt2) (@lem5103586 A lt2 s _66533 h1)). Qed.
Lemma lem5103600 {A : Type'} (s : nat -> A) (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (term134 A s) = (term167 A _66533 s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5103599 A lt2 s _66533 h1)). Qed.
Lemma lem5103601 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5103602 {A : Type'} (s : nat -> A) (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (term136 A s) = (term168 A _66533 s).
Proof. exact (MK_COMB (@lem5103601 A) (@lem5103600 A s _66533 h1)). Qed.
Lemma lem5103603 {A : Type'} (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (term138 A) = (term169 A _66533).
Proof. exact (fun_ext (fun s : nat -> A => @lem5103602 A s _66533 h1)). Qed.
Lemma lem5103604 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5103605 {A : Type'} (_66533 : type418 A) (h1 : _66533 = (term141 A)) : (term140 A) = (term170 A _66533).
Proof. exact (MK_COMB (@lem5103604 A) (@lem5103603 A _66533 h1)). Qed.
Lemma lem5103606 {A : Type'} (_66533 : type418 A) : term171 A _66533.
Proof. exact (fun h0 : _66533 = (term141 A) => @lem5103605 A _66533 h0). Qed.
Lemma lem5103607 {A : Type'} : term172 A.
Proof. exact (fun _66533 : type418 A => @lem5103606 A _66533). Qed.
Lemma lem5103609 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term173 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem5103610 {A : Type'} (P : Prop) (c : type418 A) (Q : type84 A) : term174 A P c Q.
Proof. exact (@lem5103609 (type418 A) P c Q). Qed.
Lemma lem5103611 {A : Type'} : term175 A.
Proof. exact (@lem5103610 A (term140 A) (term141 A) (term176 A)). Qed.
Lemma lem5103612 {A : Type'} (_66533 : type418 A) : (term177 A _66533) = (term170 A _66533).
Proof. exact (eq_refl (term177 A _66533)). Qed.
Lemma lem5103613 {A : Type'} : (term178 A) = (term178 A).
Proof. exact (eq_refl (term178 A)). Qed.
Lemma lem5103614 {A : Type'} (_66533 : type418 A) : ((term140 A) = (term177 A _66533)) = ((term140 A) = (term170 A _66533)).
Proof. exact (MK_COMB (@lem5103613 A) (@lem5103612 A _66533)). Qed.
Lemma lem5103615 {A : Type'} (_66533 : type418 A) : (term179 A _66533) = (term179 A _66533).
Proof. exact (eq_refl (term179 A _66533)). Qed.
Lemma lem5103616 {A : Type'} (_66533 : type418 A) : (term180 A _66533) = (term171 A _66533).
Proof. exact (MK_COMB (@lem5103615 A _66533) (@lem5103614 A _66533)). Qed.
Lemma lem5103617 {A : Type'} : (term181 A) = (term182 A).
Proof. exact (fun_ext (fun _66533 : type418 A => @lem5103616 A _66533)). Qed.
Lemma lem5103618 {A : Type'} : (@all ((A -> A -> Prop) -> A -> A -> Prop)) = (@all ((A -> A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem5103619 {A : Type'} : (term183 A) = (term172 A).
Proof. exact (MK_COMB (@lem5103618 A) (@lem5103617 A)). Qed.
Lemma lem5103620 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5103621 {A : Type'} : (term184 A) = (term185 A).
Proof. exact (MK_COMB (@lem5103620) (@lem5103619 A)). Qed.
Lemma lem5103622 {A : Type'} (_66533 : type418 A) : (term177 A _66533) = (term170 A _66533).
Proof. exact (eq_refl (term177 A _66533)). Qed.
Lemma lem5103623 {A : Type'} (_66533 : type418 A) : (term179 A _66533) = (term179 A _66533).
Proof. exact (eq_refl (term179 A _66533)). Qed.
Lemma lem5103624 {A : Type'} (_66533 : type418 A) : (term186 A _66533) = (term187 A _66533).
Proof. exact (MK_COMB (@lem5103623 A _66533) (@lem5103622 A _66533)). Qed.
Lemma lem5103625 {A : Type'} : (term188 A) = (term189 A).
Proof. exact (fun_ext (fun _66533 : type418 A => @lem5103624 A _66533)). Qed.
Lemma lem5103626 {A : Type'} : (@all ((A -> A -> Prop) -> A -> A -> Prop)) = (@all ((A -> A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem5103627 {A : Type'} : (term190 A) = (term191 A).
Proof. exact (MK_COMB (@lem5103626 A) (@lem5103625 A)). Qed.
Lemma lem5103628 {A : Type'} : (term178 A) = (term178 A).
Proof. exact (eq_refl (term178 A)). Qed.
Lemma lem5103629 {A : Type'} : ((term140 A) = (term190 A)) = ((term140 A) = (term191 A)).
Proof. exact (MK_COMB (@lem5103628 A) (@lem5103627 A)). Qed.
Lemma lem5103630 {A : Type'} : (term175 A) = (term192 A).
Proof. exact (MK_COMB (@lem5103621 A) (@lem5103629 A)). Qed.
Lemma lem5103631 {A : Type'} : term192 A.
Proof. exact (EQ_MP (@lem5103630 A) (@lem5103611 A)). Qed.
Lemma lem5103632 {A : Type'} : (term140 A) = (term191 A).
Proof. exact (@lem5103631 A (@lem5103607 A)). Qed.
Lemma lem5103634 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term193 _3571 _3575 t)) = (term194 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5103635 {A : Type'} (s : type418 A) (t : type418 A) : (s = (term195 A t)) = (term196 A s t).
Proof. exact (@lem5103634 (type1402 A) (type1402 A) s t). Qed.
Lemma lem5103636 {A : Type'} (_66533 : type418 A) : (_66533 = (term197 A)) = (term198 A _66533).
Proof. exact (@lem5103635 A _66533 (term141 A)). Qed.
Lemma lem5103637 {A : Type'} (lt2 : type1402 A) : (term142 A lt2) = (term143 A lt2).
Proof. exact (eq_refl (term142 A lt2)). Qed.
Lemma lem5103638 {A : Type'} : (term197 A) = (term141 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5103637 A lt2)). Qed.
Lemma lem5103639 {A : Type'} (_66533 : type418 A) : (@eq ((A -> A -> Prop) -> A -> A -> Prop) _66533) = (@eq ((A -> A -> Prop) -> A -> A -> Prop) _66533).
Proof. exact (eq_refl (@eq ((A -> A -> Prop) -> A -> A -> Prop) _66533)). Qed.
Lemma lem5103640 {A : Type'} (_66533 : type418 A) : (_66533 = (term197 A)) = (_66533 = (term141 A)).
Proof. exact (MK_COMB (@lem5103639 A _66533) (@lem5103638 A)). Qed.
Lemma lem5103641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5103642 {A : Type'} (_66533 : type418 A) : (term199 A _66533) = (term200 A _66533).
Proof. exact (MK_COMB (@lem5103641) (@lem5103640 A _66533)). Qed.
Lemma lem5103643 {A : Type'} (lt2 : type1402 A) : (term142 A lt2) = (term143 A lt2).
Proof. exact (eq_refl (term142 A lt2)). Qed.
Lemma lem5103644 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term144 A _66533 lt2) = (term144 A _66533 lt2).
Proof. exact (eq_refl (term144 A _66533 lt2)). Qed.
Lemma lem5103645 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : ((_66533 lt2) = (term142 A lt2)) = ((_66533 lt2) = (term143 A lt2)).
Proof. exact (MK_COMB (@lem5103644 A _66533 lt2) (@lem5103643 A lt2)). Qed.
Lemma lem5103646 {A : Type'} (_66533 : type418 A) : (term201 A _66533) = (term202 A _66533).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5103645 A _66533 lt2)). Qed.
Lemma lem5103647 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5103648 {A : Type'} (_66533 : type418 A) : (term198 A _66533) = (term203 A _66533).
Proof. exact (MK_COMB (@lem5103647 A) (@lem5103646 A _66533)). Qed.
Lemma lem5103649 {A : Type'} (_66533 : type418 A) : ((_66533 = (term197 A)) = (term198 A _66533)) = ((_66533 = (term141 A)) = (term203 A _66533)).
Proof. exact (MK_COMB (@lem5103642 A _66533) (@lem5103648 A _66533)). Qed.
Lemma lem5103650 {A : Type'} (_66533 : type418 A) : (_66533 = (term141 A)) = (term203 A _66533).
Proof. exact (EQ_MP (@lem5103649 A _66533) (@lem5103636 A _66533)). Qed.
Lemma lem5103652 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term193 _3571 _3575 t)) = (term194 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5103653 {A : Type'} (s : type1402 A) (t : type1402 A) : (s = (term204 A t)) = (term205 A s t).
Proof. exact (@lem5103652 (A -> Prop) A s t). Qed.
Lemma lem5103654 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : ((_66533 lt2) = (term206 A lt2)) = (term207 A _66533 lt2).
Proof. exact (@lem5103653 A (_66533 lt2) (term143 A lt2)). Qed.
Lemma lem5103655 {A : Type'} (lt2 : type1402 A) (x : A) : (term145 A lt2 x) = (term146 A lt2 x).
Proof. exact (eq_refl (term145 A lt2 x)). Qed.
Lemma lem5103656 {A : Type'} (lt2 : type1402 A) : (term206 A lt2) = (term143 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5103655 A lt2 x)). Qed.
Lemma lem5103657 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term144 A _66533 lt2) = (term144 A _66533 lt2).
Proof. exact (eq_refl (term144 A _66533 lt2)). Qed.
Lemma lem5103658 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : ((_66533 lt2) = (term206 A lt2)) = ((_66533 lt2) = (term143 A lt2)).
Proof. exact (MK_COMB (@lem5103657 A _66533 lt2) (@lem5103656 A lt2)). Qed.
Lemma lem5103659 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5103660 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term208 A _66533 lt2) = (term209 A _66533 lt2).
Proof. exact (MK_COMB (@lem5103659) (@lem5103658 A _66533 lt2)). Qed.
Lemma lem5103661 {A : Type'} (lt2 : type1402 A) (x : A) : (term145 A lt2 x) = (term146 A lt2 x).
Proof. exact (eq_refl (term145 A lt2 x)). Qed.
Lemma lem5103662 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term147 A _66533 lt2 x) = (term147 A _66533 lt2 x).
Proof. exact (eq_refl (term147 A _66533 lt2 x)). Qed.
Lemma lem5103663 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : ((_66533 lt2 x) = (term145 A lt2 x)) = ((_66533 lt2 x) = (term146 A lt2 x)).
Proof. exact (MK_COMB (@lem5103662 A _66533 lt2 x) (@lem5103661 A lt2 x)). Qed.
Lemma lem5103664 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term210 A _66533 lt2) = (term211 A _66533 lt2).
Proof. exact (fun_ext (fun x : A => @lem5103663 A _66533 lt2 x)). Qed.
Lemma lem5103665 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103666 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term207 A _66533 lt2) = (term212 A _66533 lt2).
Proof. exact (MK_COMB (@lem5103665 A) (@lem5103664 A _66533 lt2)). Qed.
Lemma lem5103667 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (((_66533 lt2) = (term206 A lt2)) = (term207 A _66533 lt2)) = (((_66533 lt2) = (term143 A lt2)) = (term212 A _66533 lt2)).
Proof. exact (MK_COMB (@lem5103660 A _66533 lt2) (@lem5103666 A _66533 lt2)). Qed.
Lemma lem5103668 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : ((_66533 lt2) = (term143 A lt2)) = (term212 A _66533 lt2).
Proof. exact (EQ_MP (@lem5103667 A _66533 lt2) (@lem5103654 A _66533 lt2)). Qed.
Lemma lem5103670 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term193 _3571 _3575 t)) = (term194 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5103671 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = (term213 A t)) = (term214 A s t).
Proof. exact (@lem5103670 Prop A s t). Qed.
Lemma lem5103672 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : ((_66533 lt2 x) = (term215 A lt2 x)) = (term216 A _66533 lt2 x).
Proof. exact (@lem5103671 A (_66533 lt2 x) (term146 A lt2 x)). Qed.
Lemma lem5103673 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term217 A lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term217 A lt2 x GEN_PVAR_227)). Qed.
Lemma lem5103674 {A : Type'} (lt2 : type1402 A) (x : A) : (term215 A lt2 x) = (term146 A lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5103673 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103675 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term147 A _66533 lt2 x) = (term147 A _66533 lt2 x).
Proof. exact (eq_refl (term147 A _66533 lt2 x)). Qed.
Lemma lem5103676 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : ((_66533 lt2 x) = (term215 A lt2 x)) = ((_66533 lt2 x) = (term146 A lt2 x)).
Proof. exact (MK_COMB (@lem5103675 A _66533 lt2 x) (@lem5103674 A lt2 x)). Qed.
Lemma lem5103677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5103678 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term219 A _66533 lt2 x) = (term220 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5103677) (@lem5103676 A _66533 lt2 x)). Qed.
Lemma lem5103679 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term217 A lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term217 A lt2 x GEN_PVAR_227)). Qed.
Lemma lem5103680 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term221 A _66533 lt2 x GEN_PVAR_227) = (term221 A _66533 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term221 A _66533 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5103681 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((_66533 lt2 x GEN_PVAR_227) = (term217 A lt2 x GEN_PVAR_227)) = ((_66533 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)).
Proof. exact (MK_COMB (@lem5103680 A _66533 lt2 x GEN_PVAR_227) (@lem5103679 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103682 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term222 A _66533 lt2 x) = (term223 A _66533 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5103681 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103683 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103684 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term216 A _66533 lt2 x) = (term224 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5103683 A) (@lem5103682 A _66533 lt2 x)). Qed.
Lemma lem5103685 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (((_66533 lt2 x) = (term215 A lt2 x)) = (term216 A _66533 lt2 x)) = (((_66533 lt2 x) = (term146 A lt2 x)) = (term224 A _66533 lt2 x)).
Proof. exact (MK_COMB (@lem5103678 A _66533 lt2 x) (@lem5103684 A _66533 lt2 x)). Qed.
Lemma lem5103686 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : ((_66533 lt2 x) = (term146 A lt2 x)) = (term224 A _66533 lt2 x).
Proof. exact (EQ_MP (@lem5103685 A _66533 lt2 x) (@lem5103672 A _66533 lt2 x)). Qed.
Lemma lem5103687 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((_66533 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)) = ((_66533 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)).
Proof. exact (eq_refl ((_66533 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x))). Qed.
Lemma lem5103688 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term223 A _66533 lt2 x) = (term223 A _66533 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5103687 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103689 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103690 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term224 A _66533 lt2 x) = (term224 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5103689 A) (@lem5103688 A _66533 lt2 x)). Qed.
Lemma lem5103691 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : ((_66533 lt2 x) = (term146 A lt2 x)) = (term224 A _66533 lt2 x).
Proof. exact (TRANS (@lem5103686 A _66533 lt2 x) (@lem5103690 A _66533 lt2 x)). Qed.
Lemma lem5103692 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term211 A _66533 lt2) = (term225 A _66533 lt2).
Proof. exact (fun_ext (fun x : A => @lem5103691 A _66533 lt2 x)). Qed.
Lemma lem5103693 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103694 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term212 A _66533 lt2) = (term226 A _66533 lt2).
Proof. exact (MK_COMB (@lem5103693 A) (@lem5103692 A _66533 lt2)). Qed.
Lemma lem5103695 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : ((_66533 lt2) = (term143 A lt2)) = (term226 A _66533 lt2).
Proof. exact (TRANS (@lem5103668 A _66533 lt2) (@lem5103694 A _66533 lt2)). Qed.
Lemma lem5103696 {A : Type'} (_66533 : type418 A) : (term202 A _66533) = (term227 A _66533).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5103695 A _66533 lt2)). Qed.
Lemma lem5103697 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5103698 {A : Type'} (_66533 : type418 A) : (term203 A _66533) = (term228 A _66533).
Proof. exact (MK_COMB (@lem5103697 A) (@lem5103696 A _66533)). Qed.
Lemma lem5103699 {A : Type'} (_66533 : type418 A) : (_66533 = (term141 A)) = (term228 A _66533).
Proof. exact (TRANS (@lem5103650 A _66533) (@lem5103698 A _66533)). Qed.
Lemma lem5103700 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5103701 {A : Type'} (_66533 : type418 A) : (term179 A _66533) = (term229 A _66533).
Proof. exact (MK_COMB (@lem5103700) (@lem5103699 A _66533)). Qed.
Lemma lem5103702 {A : Type'} (_66533 : type418 A) : (term170 A _66533) = (term170 A _66533).
Proof. exact (eq_refl (term170 A _66533)). Qed.
Lemma lem5103703 {A : Type'} (_66533 : type418 A) : (term187 A _66533) = (term230 A _66533).
Proof. exact (MK_COMB (@lem5103701 A _66533) (@lem5103702 A _66533)). Qed.
Lemma lem5103704 {A : Type'} : (term189 A) = (term231 A).
Proof. exact (fun_ext (fun _66533 : type418 A => @lem5103703 A _66533)). Qed.
Lemma lem5103705 {A : Type'} : (@all ((A -> A -> Prop) -> A -> A -> Prop)) = (@all ((A -> A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem5103706 {A : Type'} : (term191 A) = (term232 A).
Proof. exact (MK_COMB (@lem5103705 A) (@lem5103704 A)). Qed.
Lemma lem5103707 {A : Type'} : (term178 A) = (term178 A).
Proof. exact (eq_refl (term178 A)). Qed.
Lemma lem5103708 {A : Type'} : ((term140 A) = (term191 A)) = ((term140 A) = (term232 A)).
Proof. exact (MK_COMB (@lem5103707 A) (@lem5103706 A)). Qed.
Lemma lem5103711 {A : Type'} : (term140 A) = (term232 A).
Proof. exact (EQ_MP (@lem5103708 A) (@lem5103632 A)). Qed.
Lemma lem5103712 {A : Type'} : (term139 A) = (term232 A).
Proof. exact (TRANS (@lem5103450 A) (@lem5103711 A)). Qed.
Lemma lem5103713 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term94 A lt2 s n) = (term94 A lt2 s n).
Proof. exact (eq_refl (term94 A lt2 s n)). Qed.
Lemma lem5103714 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term96 A lt2 s) = (term96 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5103713 A lt2 s n)). Qed.
Lemma lem5103715 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5103716 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term61 A lt2 s) = (term61 A lt2 s).
Proof. exact (MK_COMB (@lem5103715) (@lem5103714 A lt2 s)). Qed.
Lemma lem5103725 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term77 A y lt2 z s x) = (term77 A y lt2 z s x).
Proof. exact (eq_refl (term77 A y lt2 z s x)). Qed.
Lemma lem5103726 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term79 A y lt2 s x) = (term79 A y lt2 s x).
Proof. exact (fun_ext (fun z : nat => @lem5103725 A y lt2 z s x)). Qed.
Lemma lem5103727 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5103728 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term81 A y lt2 s x) = (term81 A y lt2 s x).
Proof. exact (MK_COMB (@lem5103727) (@lem5103726 A y lt2 s x)). Qed.
Lemma lem5103729 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term83 A lt2 s x) = (term83 A lt2 s x).
Proof. exact (fun_ext (fun y : nat => @lem5103728 A y lt2 s x)). Qed.
Lemma lem5103730 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5103731 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term85 A lt2 s x) = (term85 A lt2 s x).
Proof. exact (MK_COMB (@lem5103730) (@lem5103729 A lt2 s x)). Qed.
Lemma lem5103732 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term87 A lt2 s) = (term87 A lt2 s).
Proof. exact (fun_ext (fun x : nat => @lem5103731 A lt2 s x)). Qed.
Lemma lem5103733 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5103734 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term89 A lt2 s) = (term89 A lt2 s).
Proof. exact (MK_COMB (@lem5103733) (@lem5103732 A lt2 s)). Qed.
Lemma lem5103735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5103736 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term91 A lt2 s) = (term91 A lt2 s).
Proof. exact (MK_COMB (@lem5103735) (@lem5103734 A lt2 s)). Qed.
Lemma lem5103737 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term99 A lt2 s) = (term99 A lt2 s).
Proof. exact (MK_COMB (@lem5103736 A lt2 s) (@lem5103716 A lt2 s)). Qed.
Lemma lem5103738 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term94 A lt2 s n) = (term94 A lt2 s n).
Proof. exact (eq_refl (term94 A lt2 s n)). Qed.
Lemma lem5103739 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term96 A lt2 s) = (term96 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5103738 A lt2 s n)). Qed.
Lemma lem5103740 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5103741 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term61 A lt2 s) = (term61 A lt2 s).
Proof. exact (MK_COMB (@lem5103740) (@lem5103739 A lt2 s)). Qed.
Lemma lem5103742 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5103743 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term122 A lt2 s) = (term122 A lt2 s).
Proof. exact (MK_COMB (@lem5103742) (@lem5103741 A lt2 s)). Qed.
Lemma lem5103744 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term124 A lt2 s) = (term124 A lt2 s).
Proof. exact (MK_COMB (@lem5103743 A lt2 s) (@lem5103737 A lt2 s)). Qed.
Lemma lem5103745 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term151 A _66533 lt2 x) = (term151 A _66533 lt2 x).
Proof. exact (eq_refl (term151 A _66533 lt2 x)). Qed.
Lemma lem5103746 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term153 A _66533 lt2) = (term153 A _66533 lt2).
Proof. exact (fun_ext (fun x : A => @lem5103745 A _66533 lt2 x)). Qed.
Lemma lem5103747 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103748 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term154 A _66533 lt2) = (term154 A _66533 lt2).
Proof. exact (MK_COMB (@lem5103747 A) (@lem5103746 A _66533 lt2)). Qed.
Lemma lem5103749 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5103750 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term155 A _66533 lt2) = (term155 A _66533 lt2).
Proof. exact (MK_COMB (@lem5103749) (@lem5103748 A _66533 lt2)). Qed.
Lemma lem5103751 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term156 A _66533 lt2 s) = (term156 A _66533 lt2 s).
Proof. exact (MK_COMB (@lem5103750 A _66533 lt2) (@lem5103744 A lt2 s)). Qed.
Lemma lem5103760 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term157 A y lt2 x z) = (term157 A y lt2 x z).
Proof. exact (eq_refl (term157 A y lt2 x z)). Qed.
Lemma lem5103761 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term158 A y lt2 x) = (term158 A y lt2 x).
Proof. exact (fun_ext (fun z : A => @lem5103760 A y lt2 x z)). Qed.
Lemma lem5103762 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103763 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term159 A y lt2 x) = (term159 A y lt2 x).
Proof. exact (MK_COMB (@lem5103762 A) (@lem5103761 A y lt2 x)). Qed.
Lemma lem5103764 {A : Type'} (lt2 : type1402 A) (x : A) : (term160 A lt2 x) = (term160 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5103763 A y lt2 x)). Qed.
Lemma lem5103765 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103766 {A : Type'} (lt2 : type1402 A) (x : A) : (term161 A lt2 x) = (term161 A lt2 x).
Proof. exact (MK_COMB (@lem5103765 A) (@lem5103764 A lt2 x)). Qed.
Lemma lem5103767 {A : Type'} (lt2 : type1402 A) : (term162 A lt2) = (term162 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5103766 A lt2 x)). Qed.
Lemma lem5103768 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103769 {A : Type'} (lt2 : type1402 A) : (term58 A lt2) = (term58 A lt2).
Proof. exact (MK_COMB (@lem5103768 A) (@lem5103767 A lt2)). Qed.
Lemma lem5103770 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5103771 {A : Type'} (lt2 : type1402 A) : (term128 A lt2) = (term128 A lt2).
Proof. exact (MK_COMB (@lem5103770) (@lem5103769 A lt2)). Qed.
Lemma lem5103772 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term163 A _66533 lt2 s) = (term163 A _66533 lt2 s).
Proof. exact (MK_COMB (@lem5103771 A lt2) (@lem5103751 A _66533 lt2 s)). Qed.
Lemma lem5103775 {A : Type'} (lt2 : type1402 A) (x : A) : (term164 A lt2 x) = (term164 A lt2 x).
Proof. exact (eq_refl (term164 A lt2 x)). Qed.
Lemma lem5103776 {A : Type'} (lt2 : type1402 A) : (term165 A lt2) = (term165 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5103775 A lt2 x)). Qed.
Lemma lem5103777 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103778 {A : Type'} (lt2 : type1402 A) : (term56 A lt2) = (term56 A lt2).
Proof. exact (MK_COMB (@lem5103777 A) (@lem5103776 A lt2)). Qed.
Lemma lem5103779 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5103780 {A : Type'} (lt2 : type1402 A) : (term131 A lt2) = (term131 A lt2).
Proof. exact (MK_COMB (@lem5103779) (@lem5103778 A lt2)). Qed.
Lemma lem5103781 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term166 A _66533 lt2 s) = (term166 A _66533 lt2 s).
Proof. exact (MK_COMB (@lem5103780 A lt2) (@lem5103772 A _66533 lt2 s)). Qed.
Lemma lem5103782 {A : Type'} (_66533 : type418 A) (s : nat -> A) : (term167 A _66533 s) = (term167 A _66533 s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5103781 A _66533 lt2 s)). Qed.
Lemma lem5103783 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5103784 {A : Type'} (_66533 : type418 A) (s : nat -> A) : (term168 A _66533 s) = (term168 A _66533 s).
Proof. exact (MK_COMB (@lem5103783 A) (@lem5103782 A _66533 s)). Qed.
Lemma lem5103785 {A : Type'} (_66533 : type418 A) : (term169 A _66533) = (term169 A _66533).
Proof. exact (fun_ext (fun s : nat -> A => @lem5103784 A _66533 s)). Qed.
Lemma lem5103786 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5103787 {A : Type'} (_66533 : type418 A) : (term170 A _66533) = (term170 A _66533).
Proof. exact (MK_COMB (@lem5103786 A) (@lem5103785 A _66533)). Qed.
Lemma lem5103788 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term233 A GEN_PVAR_227 lt2 x y) = (term233 A GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term233 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5103789 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term234 A GEN_PVAR_227 lt2 x) = (term234 A GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5103788 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5103790 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5103791 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term218 A GEN_PVAR_227 lt2 x) = (term218 A GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5103790 A) (@lem5103789 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103794 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term221 A _66533 lt2 x GEN_PVAR_227) = (term221 A _66533 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term221 A _66533 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5103795 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((_66533 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)) = ((_66533 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)).
Proof. exact (MK_COMB (@lem5103794 A _66533 lt2 x GEN_PVAR_227) (@lem5103791 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103796 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term223 A _66533 lt2 x) = (term223 A _66533 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5103795 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103797 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103798 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term224 A _66533 lt2 x) = (term224 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5103797 A) (@lem5103796 A _66533 lt2 x)). Qed.
Lemma lem5103799 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term225 A _66533 lt2) = (term225 A _66533 lt2).
Proof. exact (fun_ext (fun x : A => @lem5103798 A _66533 lt2 x)). Qed.
Lemma lem5103800 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103801 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term226 A _66533 lt2) = (term226 A _66533 lt2).
Proof. exact (MK_COMB (@lem5103800 A) (@lem5103799 A _66533 lt2)). Qed.
Lemma lem5103802 {A : Type'} (_66533 : type418 A) : (term227 A _66533) = (term227 A _66533).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5103801 A _66533 lt2)). Qed.
Lemma lem5103803 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5103804 {A : Type'} (_66533 : type418 A) : (term228 A _66533) = (term228 A _66533).
Proof. exact (MK_COMB (@lem5103803 A) (@lem5103802 A _66533)). Qed.
Lemma lem5103805 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5103806 {A : Type'} (_66533 : type418 A) : (term229 A _66533) = (term229 A _66533).
Proof. exact (MK_COMB (@lem5103805) (@lem5103804 A _66533)). Qed.
Lemma lem5103807 {A : Type'} (_66533 : type418 A) : (term230 A _66533) = (term230 A _66533).
Proof. exact (MK_COMB (@lem5103806 A _66533) (@lem5103787 A _66533)). Qed.
Lemma lem5103808 {A : Type'} : (term231 A) = (term231 A).
Proof. exact (fun_ext (fun _66533 : type418 A => @lem5103807 A _66533)). Qed.
Lemma lem5103809 {A : Type'} : (@all ((A -> A -> Prop) -> A -> A -> Prop)) = (@all ((A -> A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem5103810 {A : Type'} : (term232 A) = (term232 A).
Proof. exact (MK_COMB (@lem5103809 A) (@lem5103808 A)). Qed.
Lemma lem5103935 {A : Type'} : (term139 A) = (term232 A).
Proof. exact (TRANS (@lem5103712 A) (@lem5103810 A)). Qed.
Lemma lem5103936 {A : Type'} : (term232 A) = (term139 A).
Proof. exact (SYM (@lem5103935 A)). Qed.
Lemma lem5103937 {A : Type'} (_66533 : type418 A) (h1 : term228 A _66533) : term228 A _66533.
Proof. exact (h1). Qed.
Lemma lem5103939 {A : Type'} (lt2 : type1402 A) (h1 : term58 A lt2) : term58 A lt2.
Proof. exact (h1). Qed.
Lemma lem5103941 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term61 A lt2 s) : term61 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem5103943 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5103944 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term99 A lt2 s) = (term114 A lt2 s).
Proof. exact (@lem5103943 (term99 A lt2 s)). Qed.
Lemma lem5103945 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term114 A lt2 s) = (term99 A lt2 s).
Proof. exact (SYM (@lem5103944 A lt2 s)). Qed.
Lemma lem5103946 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term115 A lt2 s) : term115 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem5103950 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term233 A GEN_PVAR_227 lt2 x y) = (term233 A GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term233 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5103951 {A : Type'} (P : A -> Prop) : (term235 A P) = (term236 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5103952 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term237 A GEN_PVAR_227 lt2 x) = (term238 A GEN_PVAR_227 lt2 x).
Proof. exact (@lem5103951 A (term234 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103953 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term239 A GEN_PVAR_227 lt2 x y) = (term233 A GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term239 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5103954 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5103956 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term240 A GEN_PVAR_227 lt2 x y) = (term241 A GEN_PVAR_227 lt2 x y).
Proof. exact (MK_COMB (@lem5103954) (@lem5103953 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5103957 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term242 A GEN_PVAR_227 lt2 x) = (term243 A GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5103956 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5103958 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103959 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term238 A GEN_PVAR_227 lt2 x) = (term244 A GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5103958 A) (@lem5103957 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103960 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term237 A GEN_PVAR_227 lt2 x) = (term244 A GEN_PVAR_227 lt2 x).
Proof. exact (TRANS (@lem5103952 A GEN_PVAR_227 lt2 x) (@lem5103959 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103961 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term234 A GEN_PVAR_227 lt2 x) = (term234 A GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5103950 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5103962 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5103963 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term218 A GEN_PVAR_227 lt2 x) = (term218 A GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5103962 A) (@lem5103961 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103965 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term245 A _66533 lt2 x GEN_PVAR_227) = (term245 A _66533 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term245 A _66533 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5103966 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term246 A _66533 GEN_PVAR_227 lt2 x) = (term246 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5103965 A _66533 lt2 x GEN_PVAR_227) (@lem5103963 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103968 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term247 A _66533 lt2 x GEN_PVAR_227) = (term247 A _66533 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term247 A _66533 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5103969 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term248 A _66533 GEN_PVAR_227 lt2 x) = (term249 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5103968 A _66533 lt2 x GEN_PVAR_227) (@lem5103960 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5103971 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term250 A _66533 GEN_PVAR_227 lt2 x) = (term251 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5103970) (@lem5103969 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103972 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term252 A _66533 GEN_PVAR_227 lt2 x) = (term253 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5103971 A _66533 GEN_PVAR_227 lt2 x) (@lem5103966 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103973 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((_66533 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)) = (term252 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (@lem17784 (_66533 lt2 x GEN_PVAR_227) (term218 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103974 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((_66533 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)) = (term253 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (TRANS (@lem5103973 A _66533 GEN_PVAR_227 lt2 x) (@lem5103972 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103975 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term223 A _66533 lt2 x) = (term254 A _66533 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5103974 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103976 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103977 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term224 A _66533 lt2 x) = (term255 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5103976 A) (@lem5103975 A _66533 lt2 x)). Qed.
Lemma lem5103978 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term225 A _66533 lt2) = (term256 A _66533 lt2).
Proof. exact (fun_ext (fun x : A => @lem5103977 A _66533 lt2 x)). Qed.
Lemma lem5103979 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5103980 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term226 A _66533 lt2) = (term257 A _66533 lt2).
Proof. exact (MK_COMB (@lem5103979 A) (@lem5103978 A _66533 lt2)). Qed.
Lemma lem5103981 {A : Type'} (_66533 : type418 A) : (term227 A _66533) = (term258 A _66533).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5103980 A _66533 lt2)). Qed.
Lemma lem5103982 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5103983 {A : Type'} (_66533 : type418 A) : (term228 A _66533) = (term259 A _66533).
Proof. exact (MK_COMB (@lem5103982 A) (@lem5103981 A _66533)). Qed.
Lemma lem5103993 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5103994 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (@lem5103993 A P Q). Qed.
Lemma lem5103995 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term262 A _66533 lt2 x) = (term263 A _66533 lt2 x).
Proof. exact (@lem5103994 A (term264 A _66533 lt2 x) (term265 A _66533 lt2 x)). Qed.
Lemma lem5103996 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term266 A _66533 lt2 x GEN_PVAR_227) = (term249 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term266 A _66533 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5103997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5103998 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term267 A _66533 lt2 x GEN_PVAR_227) = (term251 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5103997) (@lem5103996 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5103999 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term268 A _66533 lt2 x GEN_PVAR_227) = (term246 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term268 A _66533 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5104000 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term269 A _66533 lt2 x GEN_PVAR_227) = (term253 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5103998 A _66533 GEN_PVAR_227 lt2 x) (@lem5103999 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5104001 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term270 A _66533 lt2 x) = (term254 A _66533 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5104000 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5104002 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104003 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term262 A _66533 lt2 x) = (term255 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5104002 A) (@lem5104001 A _66533 lt2 x)). Qed.
Lemma lem5104004 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5104005 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term271 A _66533 lt2 x) = (term272 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5104004) (@lem5104003 A _66533 lt2 x)). Qed.
Lemma lem5104006 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term266 A _66533 lt2 x GEN_PVAR_227) = (term249 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term266 A _66533 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5104007 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term273 A _66533 lt2 x) = (term264 A _66533 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5104006 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5104008 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104009 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term274 A _66533 lt2 x) = (term275 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5104008 A) (@lem5104007 A _66533 lt2 x)). Qed.
Lemma lem5104010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5104011 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term276 A _66533 lt2 x) = (term277 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5104010) (@lem5104009 A _66533 lt2 x)). Qed.
Lemma lem5104012 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term268 A _66533 lt2 x GEN_PVAR_227) = (term246 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term268 A _66533 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5104013 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term278 A _66533 lt2 x) = (term265 A _66533 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5104012 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5104014 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104015 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term279 A _66533 lt2 x) = (term280 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5104014 A) (@lem5104013 A _66533 lt2 x)). Qed.
Lemma lem5104016 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term263 A _66533 lt2 x) = (term281 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5104011 A _66533 lt2 x) (@lem5104015 A _66533 lt2 x)). Qed.
Lemma lem5104017 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : ((term262 A _66533 lt2 x) = (term263 A _66533 lt2 x)) = ((term255 A _66533 lt2 x) = (term281 A _66533 lt2 x)).
Proof. exact (MK_COMB (@lem5104005 A _66533 lt2 x) (@lem5104016 A _66533 lt2 x)). Qed.
Lemma lem5104018 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term255 A _66533 lt2 x) = (term281 A _66533 lt2 x).
Proof. exact (EQ_MP (@lem5104017 A _66533 lt2 x) (@lem5103995 A _66533 lt2 x)). Qed.
Lemma lem5104123 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term256 A _66533 lt2) = (term282 A _66533 lt2).
Proof. exact (fun_ext (fun x : A => @lem5104018 A _66533 lt2 x)). Qed.
Lemma lem5104124 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104125 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term257 A _66533 lt2) = (term283 A _66533 lt2).
Proof. exact (MK_COMB (@lem5104124 A) (@lem5104123 A _66533 lt2)). Qed.
Lemma lem5104127 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5104128 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (@lem5104127 A P Q). Qed.
Lemma lem5104129 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term284 A _66533 lt2) = (term285 A _66533 lt2).
Proof. exact (@lem5104128 A (term286 A _66533 lt2) (term287 A _66533 lt2)). Qed.
Lemma lem5104130 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term288 A _66533 lt2 x) = (term275 A _66533 lt2 x).
Proof. exact (eq_refl (term288 A _66533 lt2 x)). Qed.
Lemma lem5104131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5104132 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term289 A _66533 lt2 x) = (term277 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5104131) (@lem5104130 A _66533 lt2 x)). Qed.
Lemma lem5104133 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term290 A _66533 lt2 x) = (term280 A _66533 lt2 x).
Proof. exact (eq_refl (term290 A _66533 lt2 x)). Qed.
Lemma lem5104134 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term291 A _66533 lt2 x) = (term281 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5104132 A _66533 lt2 x) (@lem5104133 A _66533 lt2 x)). Qed.
Lemma lem5104135 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term292 A _66533 lt2) = (term282 A _66533 lt2).
Proof. exact (fun_ext (fun x : A => @lem5104134 A _66533 lt2 x)). Qed.
Lemma lem5104136 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104137 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term284 A _66533 lt2) = (term283 A _66533 lt2).
Proof. exact (MK_COMB (@lem5104136 A) (@lem5104135 A _66533 lt2)). Qed.
Lemma lem5104138 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5104139 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term293 A _66533 lt2) = (term294 A _66533 lt2).
Proof. exact (MK_COMB (@lem5104138) (@lem5104137 A _66533 lt2)). Qed.
Lemma lem5104140 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term288 A _66533 lt2 x) = (term275 A _66533 lt2 x).
Proof. exact (eq_refl (term288 A _66533 lt2 x)). Qed.
Lemma lem5104141 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term295 A _66533 lt2) = (term286 A _66533 lt2).
Proof. exact (fun_ext (fun x : A => @lem5104140 A _66533 lt2 x)). Qed.
Lemma lem5104142 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104143 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term296 A _66533 lt2) = (term297 A _66533 lt2).
Proof. exact (MK_COMB (@lem5104142 A) (@lem5104141 A _66533 lt2)). Qed.
Lemma lem5104144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5104145 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term298 A _66533 lt2) = (term299 A _66533 lt2).
Proof. exact (MK_COMB (@lem5104144) (@lem5104143 A _66533 lt2)). Qed.
Lemma lem5104146 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term290 A _66533 lt2 x) = (term280 A _66533 lt2 x).
Proof. exact (eq_refl (term290 A _66533 lt2 x)). Qed.
Lemma lem5104147 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term300 A _66533 lt2) = (term287 A _66533 lt2).
Proof. exact (fun_ext (fun x : A => @lem5104146 A _66533 lt2 x)). Qed.
Lemma lem5104148 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104149 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term301 A _66533 lt2) = (term302 A _66533 lt2).
Proof. exact (MK_COMB (@lem5104148 A) (@lem5104147 A _66533 lt2)). Qed.
Lemma lem5104150 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term285 A _66533 lt2) = (term303 A _66533 lt2).
Proof. exact (MK_COMB (@lem5104145 A _66533 lt2) (@lem5104149 A _66533 lt2)). Qed.
Lemma lem5104151 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : ((term284 A _66533 lt2) = (term285 A _66533 lt2)) = ((term283 A _66533 lt2) = (term303 A _66533 lt2)).
Proof. exact (MK_COMB (@lem5104139 A _66533 lt2) (@lem5104150 A _66533 lt2)). Qed.
Lemma lem5104152 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term283 A _66533 lt2) = (term303 A _66533 lt2).
Proof. exact (EQ_MP (@lem5104151 A _66533 lt2) (@lem5104129 A _66533 lt2)). Qed.
Lemma lem5104265 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term257 A _66533 lt2) = (term303 A _66533 lt2).
Proof. exact (TRANS (@lem5104125 A _66533 lt2) (@lem5104152 A _66533 lt2)). Qed.
Lemma lem5104266 {A : Type'} (_66533 : type418 A) : (term258 A _66533) = (term304 A _66533).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5104265 A _66533 lt2)). Qed.
Lemma lem5104267 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5104268 {A : Type'} (_66533 : type418 A) : (term259 A _66533) = (term305 A _66533).
Proof. exact (MK_COMB (@lem5104267 A) (@lem5104266 A _66533)). Qed.
Lemma lem5104270 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5104271 {A : Type'} (P : type421 A) (Q : type421 A) : (term306 A P Q) = (term307 A P Q).
Proof. exact (@lem5104270 (type1402 A) P Q). Qed.
Lemma lem5104272 {A : Type'} (_66533 : type418 A) : (term308 A _66533) = (term309 A _66533).
Proof. exact (@lem5104271 A (term310 A _66533) (term311 A _66533)). Qed.
Lemma lem5104273 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term312 A _66533 lt2) = (term297 A _66533 lt2).
Proof. exact (eq_refl (term312 A _66533 lt2)). Qed.
Lemma lem5104274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5104275 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term313 A _66533 lt2) = (term299 A _66533 lt2).
Proof. exact (MK_COMB (@lem5104274) (@lem5104273 A _66533 lt2)). Qed.
Lemma lem5104276 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term314 A _66533 lt2) = (term302 A _66533 lt2).
Proof. exact (eq_refl (term314 A _66533 lt2)). Qed.
Lemma lem5104277 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term315 A _66533 lt2) = (term303 A _66533 lt2).
Proof. exact (MK_COMB (@lem5104275 A _66533 lt2) (@lem5104276 A _66533 lt2)). Qed.
Lemma lem5104278 {A : Type'} (_66533 : type418 A) : (term316 A _66533) = (term304 A _66533).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5104277 A _66533 lt2)). Qed.
Lemma lem5104279 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5104280 {A : Type'} (_66533 : type418 A) : (term308 A _66533) = (term305 A _66533).
Proof. exact (MK_COMB (@lem5104279 A) (@lem5104278 A _66533)). Qed.
Lemma lem5104281 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5104282 {A : Type'} (_66533 : type418 A) : (term317 A _66533) = (term318 A _66533).
Proof. exact (MK_COMB (@lem5104281) (@lem5104280 A _66533)). Qed.
Lemma lem5104283 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term312 A _66533 lt2) = (term297 A _66533 lt2).
Proof. exact (eq_refl (term312 A _66533 lt2)). Qed.
Lemma lem5104284 {A : Type'} (_66533 : type418 A) : (term319 A _66533) = (term310 A _66533).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5104283 A _66533 lt2)). Qed.
Lemma lem5104285 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5104286 {A : Type'} (_66533 : type418 A) : (term320 A _66533) = (term321 A _66533).
Proof. exact (MK_COMB (@lem5104285 A) (@lem5104284 A _66533)). Qed.
Lemma lem5104287 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5104288 {A : Type'} (_66533 : type418 A) : (term322 A _66533) = (term323 A _66533).
Proof. exact (MK_COMB (@lem5104287) (@lem5104286 A _66533)). Qed.
Lemma lem5104289 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term314 A _66533 lt2) = (term302 A _66533 lt2).
Proof. exact (eq_refl (term314 A _66533 lt2)). Qed.
Lemma lem5104290 {A : Type'} (_66533 : type418 A) : (term324 A _66533) = (term311 A _66533).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5104289 A _66533 lt2)). Qed.
Lemma lem5104291 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5104292 {A : Type'} (_66533 : type418 A) : (term325 A _66533) = (term326 A _66533).
Proof. exact (MK_COMB (@lem5104291 A) (@lem5104290 A _66533)). Qed.
Lemma lem5104293 {A : Type'} (_66533 : type418 A) : (term309 A _66533) = (term327 A _66533).
Proof. exact (MK_COMB (@lem5104288 A _66533) (@lem5104292 A _66533)). Qed.
Lemma lem5104294 {A : Type'} (_66533 : type418 A) : ((term308 A _66533) = (term309 A _66533)) = ((term305 A _66533) = (term327 A _66533)).
Proof. exact (MK_COMB (@lem5104282 A _66533) (@lem5104293 A _66533)). Qed.
Lemma lem5104295 {A : Type'} (_66533 : type418 A) : (term305 A _66533) = (term327 A _66533).
Proof. exact (EQ_MP (@lem5104294 A _66533) (@lem5104272 A _66533)). Qed.
Lemma lem5104416 {A : Type'} (_66533 : type418 A) : (term259 A _66533) = (term327 A _66533).
Proof. exact (TRANS (@lem5104268 A _66533) (@lem5104295 A _66533)). Qed.
Lemma lem5104418 {A : Type'} (P : Prop) (Q : A -> Prop) : (term328 A P Q) = (term329 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5104419 {A : Type'} (P : Prop) (Q : A -> Prop) : (term328 A P Q) = (term329 A P Q).
Proof. exact (@lem5104418 A P Q). Qed.
Lemma lem5104420 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term330 A _66533 GEN_PVAR_227 lt2 x) = (term331 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (@lem5104419 A (term332 A _66533 lt2 x GEN_PVAR_227) (term234 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5104421 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term239 A GEN_PVAR_227 lt2 x y) = (term233 A GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term239 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5104422 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term333 A GEN_PVAR_227 lt2 x) = (term234 A GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5104421 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5104423 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5104424 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term334 A GEN_PVAR_227 lt2 x) = (term218 A GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5104423 A) (@lem5104422 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5104425 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term245 A _66533 lt2 x GEN_PVAR_227) = (term245 A _66533 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term245 A _66533 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5104426 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term330 A _66533 GEN_PVAR_227 lt2 x) = (term246 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5104425 A _66533 lt2 x GEN_PVAR_227) (@lem5104424 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5104427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5104428 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term335 A _66533 GEN_PVAR_227 lt2 x) = (term336 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5104427) (@lem5104426 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5104429 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term239 A GEN_PVAR_227 lt2 x y) = (term233 A GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term239 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5104430 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term245 A _66533 lt2 x GEN_PVAR_227) = (term245 A _66533 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term245 A _66533 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5104431 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term337 A _66533 GEN_PVAR_227 lt2 x y) = (term338 A _66533 GEN_PVAR_227 lt2 x y).
Proof. exact (MK_COMB (@lem5104430 A _66533 lt2 x GEN_PVAR_227) (@lem5104429 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5104432 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term339 A _66533 GEN_PVAR_227 lt2 x) = (term340 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5104431 A _66533 GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5104433 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5104434 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term331 A _66533 GEN_PVAR_227 lt2 x) = (term341 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5104433 A) (@lem5104432 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5104435 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((term330 A _66533 GEN_PVAR_227 lt2 x) = (term331 A _66533 GEN_PVAR_227 lt2 x)) = ((term246 A _66533 GEN_PVAR_227 lt2 x) = (term341 A _66533 GEN_PVAR_227 lt2 x)).
Proof. exact (MK_COMB (@lem5104428 A _66533 GEN_PVAR_227 lt2 x) (@lem5104434 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5104436 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term246 A _66533 GEN_PVAR_227 lt2 x) = (term341 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (EQ_MP (@lem5104435 A _66533 GEN_PVAR_227 lt2 x) (@lem5104420 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5104437 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term265 A _66533 lt2 x) = (term342 A _66533 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5104436 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5104438 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104439 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term280 A _66533 lt2 x) = (term343 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5104438 A) (@lem5104437 A _66533 lt2 x)). Qed.
Lemma lem5104441 {A B : Type'} (P : type1413 A B) : (term344 A B P) = (term345 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5104442 {A : Type'} (P : type1402 A) : (term346 A P) = (term347 A P).
Proof. exact (@lem5104441 A A P). Qed.
Lemma lem5104443 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term348 A _66533 lt2 x) = (term349 A _66533 lt2 x).
Proof. exact (@lem5104442 A (term350 A _66533 lt2 x)). Qed.
Lemma lem5104444 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term351 A _66533 lt2 x GEN_PVAR_227) = (term340 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term351 A _66533 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5104445 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5104446 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term352 A _66533 lt2 x GEN_PVAR_227 y) = (term353 A _66533 GEN_PVAR_227 lt2 x y).
Proof. exact (MK_COMB (@lem5104444 A _66533 GEN_PVAR_227 lt2 x) (@lem5104445 A y)). Qed.
Lemma lem5104447 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term353 A _66533 GEN_PVAR_227 lt2 x y) = (term338 A _66533 GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term353 A _66533 GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5104448 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term352 A _66533 lt2 x GEN_PVAR_227 y) = (term338 A _66533 GEN_PVAR_227 lt2 x y).
Proof. exact (TRANS (@lem5104446 A _66533 GEN_PVAR_227 lt2 x y) (@lem5104447 A _66533 GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5104449 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term354 A _66533 lt2 x GEN_PVAR_227) = (term340 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5104448 A _66533 GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5104450 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5104451 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term355 A _66533 lt2 x GEN_PVAR_227) = (term341 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5104450 A) (@lem5104449 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5104452 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term356 A _66533 lt2 x) = (term342 A _66533 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5104451 A _66533 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5104453 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104454 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term348 A _66533 lt2 x) = (term343 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5104453 A) (@lem5104452 A _66533 lt2 x)). Qed.
Lemma lem5104455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5104456 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term357 A _66533 lt2 x) = (term358 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5104455) (@lem5104454 A _66533 lt2 x)). Qed.
Lemma lem5104457 {A : Type'} (_66533 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term351 A _66533 lt2 x GEN_PVAR_227) = (term340 A _66533 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term351 A _66533 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5104458 {A : Type'} (y : A -> A) (GEN_PVAR_227 : A) : (y GEN_PVAR_227) = (y GEN_PVAR_227).
Proof. exact (eq_refl (y GEN_PVAR_227)). Qed.
Lemma lem5104459 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) (GEN_PVAR_227 : A) : (term359 A _66533 lt2 x y GEN_PVAR_227) = (term360 A _66533 lt2 x y GEN_PVAR_227).
Proof. exact (MK_COMB (@lem5104457 A _66533 GEN_PVAR_227 lt2 x) (@lem5104458 A y GEN_PVAR_227)). Qed.
Lemma lem5104460 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) (GEN_PVAR_227 : A) : (term360 A _66533 lt2 x y GEN_PVAR_227) = (term361 A _66533 lt2 x y GEN_PVAR_227).
Proof. exact (eq_refl (term360 A _66533 lt2 x y GEN_PVAR_227)). Qed.
Lemma lem5104461 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) (GEN_PVAR_227 : A) : (term359 A _66533 lt2 x y GEN_PVAR_227) = (term361 A _66533 lt2 x y GEN_PVAR_227).
Proof. exact (TRANS (@lem5104459 A _66533 lt2 x y GEN_PVAR_227) (@lem5104460 A _66533 lt2 x y GEN_PVAR_227)). Qed.
Lemma lem5104462 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) : (term362 A _66533 lt2 x y) = (term363 A _66533 lt2 x y).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5104461 A _66533 lt2 x y GEN_PVAR_227)). Qed.
Lemma lem5104463 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104464 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) : (term364 A _66533 lt2 x y) = (term365 A _66533 lt2 x y).
Proof. exact (MK_COMB (@lem5104463 A) (@lem5104462 A _66533 lt2 x y)). Qed.
Lemma lem5104465 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term366 A _66533 lt2 x) = (term367 A _66533 lt2 x).
Proof. exact (fun_ext (fun y : A -> A => @lem5104464 A _66533 lt2 x y)). Qed.
Lemma lem5104466 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem5104467 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term349 A _66533 lt2 x) = (term368 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5104466 A) (@lem5104465 A _66533 lt2 x)). Qed.
Lemma lem5104468 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : ((term348 A _66533 lt2 x) = (term349 A _66533 lt2 x)) = ((term343 A _66533 lt2 x) = (term368 A _66533 lt2 x)).
Proof. exact (MK_COMB (@lem5104456 A _66533 lt2 x) (@lem5104467 A _66533 lt2 x)). Qed.
Lemma lem5104469 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term343 A _66533 lt2 x) = (term368 A _66533 lt2 x).
Proof. exact (EQ_MP (@lem5104468 A _66533 lt2 x) (@lem5104443 A _66533 lt2 x)). Qed.
Lemma lem5104470 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term280 A _66533 lt2 x) = (term368 A _66533 lt2 x).
Proof. exact (TRANS (@lem5104439 A _66533 lt2 x) (@lem5104469 A _66533 lt2 x)). Qed.
Lemma lem5104471 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term287 A _66533 lt2) = (term369 A _66533 lt2).
Proof. exact (fun_ext (fun x : A => @lem5104470 A _66533 lt2 x)). Qed.
Lemma lem5104472 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104473 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term302 A _66533 lt2) = (term370 A _66533 lt2).
Proof. exact (MK_COMB (@lem5104472 A) (@lem5104471 A _66533 lt2)). Qed.
Lemma lem5104475 {A B : Type'} (P : type1413 A B) : (term344 A B P) = (term345 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5104476 {A : Type'} (P : type1359 A) : (term371 A P) = (term372 A P).
Proof. exact (@lem5104475 A (A -> A) P). Qed.
Lemma lem5104477 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term373 A _66533 lt2) = (term374 A _66533 lt2).
Proof. exact (@lem5104476 A (term375 A _66533 lt2)). Qed.
Lemma lem5104478 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term376 A _66533 lt2 x) = (term367 A _66533 lt2 x).
Proof. exact (eq_refl (term376 A _66533 lt2 x)). Qed.
Lemma lem5104479 {A : Type'} (y : A -> A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5104480 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) : (term377 A _66533 lt2 x y) = (term378 A _66533 lt2 x y).
Proof. exact (MK_COMB (@lem5104478 A _66533 lt2 x) (@lem5104479 A y)). Qed.
Lemma lem5104481 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) : (term378 A _66533 lt2 x y) = (term365 A _66533 lt2 x y).
Proof. exact (eq_refl (term378 A _66533 lt2 x y)). Qed.
Lemma lem5104482 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) : (term377 A _66533 lt2 x y) = (term365 A _66533 lt2 x y).
Proof. exact (TRANS (@lem5104480 A _66533 lt2 x y) (@lem5104481 A _66533 lt2 x y)). Qed.
Lemma lem5104483 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term379 A _66533 lt2 x) = (term367 A _66533 lt2 x).
Proof. exact (fun_ext (fun y : A -> A => @lem5104482 A _66533 lt2 x y)). Qed.
Lemma lem5104484 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem5104485 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term380 A _66533 lt2 x) = (term368 A _66533 lt2 x).
Proof. exact (MK_COMB (@lem5104484 A) (@lem5104483 A _66533 lt2 x)). Qed.
Lemma lem5104486 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term381 A _66533 lt2) = (term369 A _66533 lt2).
Proof. exact (fun_ext (fun x : A => @lem5104485 A _66533 lt2 x)). Qed.
Lemma lem5104487 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104488 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term373 A _66533 lt2) = (term370 A _66533 lt2).
Proof. exact (MK_COMB (@lem5104487 A) (@lem5104486 A _66533 lt2)). Qed.
Lemma lem5104489 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5104490 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term382 A _66533 lt2) = (term383 A _66533 lt2).
Proof. exact (MK_COMB (@lem5104489) (@lem5104488 A _66533 lt2)). Qed.
Lemma lem5104491 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (x : A) : (term376 A _66533 lt2 x) = (term367 A _66533 lt2 x).
Proof. exact (eq_refl (term376 A _66533 lt2 x)). Qed.
Lemma lem5104492 {A : Type'} (y : type1400 A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem5104493 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (y : type1400 A) (x : A) : (term384 A _66533 lt2 y x) = (term385 A _66533 lt2 y x).
Proof. exact (MK_COMB (@lem5104491 A _66533 lt2 x) (@lem5104492 A y x)). Qed.
Lemma lem5104494 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (y : type1400 A) (x : A) : (term385 A _66533 lt2 y x) = (term386 A _66533 lt2 y x).
Proof. exact (eq_refl (term385 A _66533 lt2 y x)). Qed.
Lemma lem5104495 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (y : type1400 A) (x : A) : (term384 A _66533 lt2 y x) = (term386 A _66533 lt2 y x).
Proof. exact (TRANS (@lem5104493 A _66533 lt2 y x) (@lem5104494 A _66533 lt2 y x)). Qed.
Lemma lem5104496 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (y : type1400 A) : (term387 A _66533 lt2 y) = (term388 A _66533 lt2 y).
Proof. exact (fun_ext (fun x : A => @lem5104495 A _66533 lt2 y x)). Qed.
Lemma lem5104497 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104498 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (y : type1400 A) : (term389 A _66533 lt2 y) = (term390 A _66533 lt2 y).
Proof. exact (MK_COMB (@lem5104497 A) (@lem5104496 A _66533 lt2 y)). Qed.
Lemma lem5104499 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term391 A _66533 lt2) = (term392 A _66533 lt2).
Proof. exact (fun_ext (fun y : type1400 A => @lem5104498 A _66533 lt2 y)). Qed.
Lemma lem5104500 {A : Type'} : (@ex (A -> A -> A)) = (@ex (A -> A -> A)).
Proof. exact (eq_refl (@ex (A -> A -> A))). Qed.
Lemma lem5104501 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term374 A _66533 lt2) = (term393 A _66533 lt2).
Proof. exact (MK_COMB (@lem5104500 A) (@lem5104499 A _66533 lt2)). Qed.
Lemma lem5104502 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : ((term373 A _66533 lt2) = (term374 A _66533 lt2)) = ((term370 A _66533 lt2) = (term393 A _66533 lt2)).
Proof. exact (MK_COMB (@lem5104490 A _66533 lt2) (@lem5104501 A _66533 lt2)). Qed.
Lemma lem5104503 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term370 A _66533 lt2) = (term393 A _66533 lt2).
Proof. exact (EQ_MP (@lem5104502 A _66533 lt2) (@lem5104477 A _66533 lt2)). Qed.
Lemma lem5104504 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term302 A _66533 lt2) = (term393 A _66533 lt2).
Proof. exact (TRANS (@lem5104473 A _66533 lt2) (@lem5104503 A _66533 lt2)). Qed.
Lemma lem5104505 {A : Type'} (_66533 : type418 A) : (term311 A _66533) = (term394 A _66533).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5104504 A _66533 lt2)). Qed.
Lemma lem5104506 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5104507 {A : Type'} (_66533 : type418 A) : (term326 A _66533) = (term395 A _66533).
Proof. exact (MK_COMB (@lem5104506 A) (@lem5104505 A _66533)). Qed.
Lemma lem5104509 {A B : Type'} (P : type1413 A B) : (term344 A B P) = (term345 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5104510 {A : Type'} (P : type412 A) : (term396 A P) = (term397 A P).
Proof. exact (@lem5104509 (type1402 A) (type1400 A) P). Qed.
Lemma lem5104511 {A : Type'} (_66533 : type418 A) : (term398 A _66533) = (term399 A _66533).
Proof. exact (@lem5104510 A (term400 A _66533)). Qed.
Lemma lem5104512 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term401 A _66533 lt2) = (term392 A _66533 lt2).
Proof. exact (eq_refl (term401 A _66533 lt2)). Qed.
Lemma lem5104513 {A : Type'} (y : type1400 A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5104514 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (y : type1400 A) : (term402 A _66533 lt2 y) = (term403 A _66533 lt2 y).
Proof. exact (MK_COMB (@lem5104512 A _66533 lt2) (@lem5104513 A y)). Qed.
Lemma lem5104515 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (y : type1400 A) : (term403 A _66533 lt2 y) = (term390 A _66533 lt2 y).
Proof. exact (eq_refl (term403 A _66533 lt2 y)). Qed.
Lemma lem5104516 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (y : type1400 A) : (term402 A _66533 lt2 y) = (term390 A _66533 lt2 y).
Proof. exact (TRANS (@lem5104514 A _66533 lt2 y) (@lem5104515 A _66533 lt2 y)). Qed.
Lemma lem5104517 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term404 A _66533 lt2) = (term392 A _66533 lt2).
Proof. exact (fun_ext (fun y : type1400 A => @lem5104516 A _66533 lt2 y)). Qed.
Lemma lem5104518 {A : Type'} : (@ex (A -> A -> A)) = (@ex (A -> A -> A)).
Proof. exact (eq_refl (@ex (A -> A -> A))). Qed.
Lemma lem5104519 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term405 A _66533 lt2) = (term393 A _66533 lt2).
Proof. exact (MK_COMB (@lem5104518 A) (@lem5104517 A _66533 lt2)). Qed.
Lemma lem5104520 {A : Type'} (_66533 : type418 A) : (term406 A _66533) = (term394 A _66533).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5104519 A _66533 lt2)). Qed.
Lemma lem5104521 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5104522 {A : Type'} (_66533 : type418 A) : (term398 A _66533) = (term395 A _66533).
Proof. exact (MK_COMB (@lem5104521 A) (@lem5104520 A _66533)). Qed.
Lemma lem5104523 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5104524 {A : Type'} (_66533 : type418 A) : (term407 A _66533) = (term408 A _66533).
Proof. exact (MK_COMB (@lem5104523) (@lem5104522 A _66533)). Qed.
Lemma lem5104525 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) : (term401 A _66533 lt2) = (term392 A _66533 lt2).
Proof. exact (eq_refl (term401 A _66533 lt2)). Qed.
Lemma lem5104526 {A : Type'} (y : type417 A) (lt2 : type1402 A) : (y lt2) = (y lt2).
Proof. exact (eq_refl (y lt2)). Qed.
Lemma lem5104527 {A : Type'} (_66533 : type418 A) (y : type417 A) (lt2 : type1402 A) : (term409 A _66533 y lt2) = (term410 A _66533 y lt2).
Proof. exact (MK_COMB (@lem5104525 A _66533 lt2) (@lem5104526 A y lt2)). Qed.
Lemma lem5104528 {A : Type'} (_66533 : type418 A) (y : type417 A) (lt2 : type1402 A) : (term410 A _66533 y lt2) = (term411 A _66533 y lt2).
Proof. exact (eq_refl (term410 A _66533 y lt2)). Qed.
Lemma lem5104529 {A : Type'} (_66533 : type418 A) (y : type417 A) (lt2 : type1402 A) : (term409 A _66533 y lt2) = (term411 A _66533 y lt2).
Proof. exact (TRANS (@lem5104527 A _66533 y lt2) (@lem5104528 A _66533 y lt2)). Qed.
Lemma lem5104530 {A : Type'} (_66533 : type418 A) (y : type417 A) : (term412 A _66533 y) = (term413 A _66533 y).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5104529 A _66533 y lt2)). Qed.
Lemma lem5104531 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5104532 {A : Type'} (_66533 : type418 A) (y : type417 A) : (term414 A _66533 y) = (term415 A _66533 y).
Proof. exact (MK_COMB (@lem5104531 A) (@lem5104530 A _66533 y)). Qed.
Lemma lem5104533 {A : Type'} (_66533 : type418 A) : (term416 A _66533) = (term417 A _66533).
Proof. exact (fun_ext (fun y : type417 A => @lem5104532 A _66533 y)). Qed.
Lemma lem5104534 {A : Type'} : (@ex ((A -> A -> Prop) -> A -> A -> A)) = (@ex ((A -> A -> Prop) -> A -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> A -> A -> A))). Qed.
Lemma lem5104535 {A : Type'} (_66533 : type418 A) : (term399 A _66533) = (term418 A _66533).
Proof. exact (MK_COMB (@lem5104534 A) (@lem5104533 A _66533)). Qed.
Lemma lem5104536 {A : Type'} (_66533 : type418 A) : ((term398 A _66533) = (term399 A _66533)) = ((term395 A _66533) = (term418 A _66533)).
Proof. exact (MK_COMB (@lem5104524 A _66533) (@lem5104535 A _66533)). Qed.
Lemma lem5104537 {A : Type'} (_66533 : type418 A) : (term395 A _66533) = (term418 A _66533).
Proof. exact (EQ_MP (@lem5104536 A _66533) (@lem5104511 A _66533)). Qed.
Lemma lem5104538 {A : Type'} (_66533 : type418 A) : (term326 A _66533) = (term418 A _66533).
Proof. exact (TRANS (@lem5104507 A _66533) (@lem5104537 A _66533)). Qed.
Lemma lem5104539 {A : Type'} (_66533 : type418 A) : (term323 A _66533) = (term323 A _66533).
Proof. exact (eq_refl (term323 A _66533)). Qed.
Lemma lem5104540 {A : Type'} (_66533 : type418 A) : (term327 A _66533) = (term419 A _66533).
Proof. exact (MK_COMB (@lem5104539 A _66533) (@lem5104538 A _66533)). Qed.
Lemma lem5104542 {A : Type'} (P : Prop) (Q : A -> Prop) : (term420 A P Q) = (term421 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5104543 {A : Type'} (P : Prop) (Q : type83 A) : (term422 A P Q) = (term423 A P Q).
Proof. exact (@lem5104542 (type417 A) P Q). Qed.
Lemma lem5104544 {A : Type'} (_66533 : type418 A) : (term424 A _66533) = (term425 A _66533).
Proof. exact (@lem5104543 A (term321 A _66533) (term417 A _66533)). Qed.
Lemma lem5104545 {A : Type'} (_66533 : type418 A) (y : type417 A) : (term426 A _66533 y) = (term415 A _66533 y).
Proof. exact (eq_refl (term426 A _66533 y)). Qed.
Lemma lem5104546 {A : Type'} (_66533 : type418 A) : (term427 A _66533) = (term417 A _66533).
Proof. exact (fun_ext (fun y : type417 A => @lem5104545 A _66533 y)). Qed.
Lemma lem5104547 {A : Type'} : (@ex ((A -> A -> Prop) -> A -> A -> A)) = (@ex ((A -> A -> Prop) -> A -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> A -> A -> A))). Qed.
Lemma lem5104548 {A : Type'} (_66533 : type418 A) : (term428 A _66533) = (term418 A _66533).
Proof. exact (MK_COMB (@lem5104547 A) (@lem5104546 A _66533)). Qed.
Lemma lem5104549 {A : Type'} (_66533 : type418 A) : (term323 A _66533) = (term323 A _66533).
Proof. exact (eq_refl (term323 A _66533)). Qed.
Lemma lem5104550 {A : Type'} (_66533 : type418 A) : (term424 A _66533) = (term419 A _66533).
Proof. exact (MK_COMB (@lem5104549 A _66533) (@lem5104548 A _66533)). Qed.
Lemma lem5104551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5104552 {A : Type'} (_66533 : type418 A) : (term429 A _66533) = (term430 A _66533).
Proof. exact (MK_COMB (@lem5104551) (@lem5104550 A _66533)). Qed.
Lemma lem5104553 {A : Type'} (_66533 : type418 A) (y : type417 A) : (term426 A _66533 y) = (term415 A _66533 y).
Proof. exact (eq_refl (term426 A _66533 y)). Qed.
Lemma lem5104554 {A : Type'} (_66533 : type418 A) : (term323 A _66533) = (term323 A _66533).
Proof. exact (eq_refl (term323 A _66533)). Qed.
Lemma lem5104555 {A : Type'} (_66533 : type418 A) (y : type417 A) : (term431 A _66533 y) = (term432 A _66533 y).
Proof. exact (MK_COMB (@lem5104554 A _66533) (@lem5104553 A _66533 y)). Qed.
Lemma lem5104556 {A : Type'} (_66533 : type418 A) : (term433 A _66533) = (term434 A _66533).
Proof. exact (fun_ext (fun y : type417 A => @lem5104555 A _66533 y)). Qed.
Lemma lem5104557 {A : Type'} : (@ex ((A -> A -> Prop) -> A -> A -> A)) = (@ex ((A -> A -> Prop) -> A -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> A -> A -> A))). Qed.
Lemma lem5104558 {A : Type'} (_66533 : type418 A) : (term425 A _66533) = (term435 A _66533).
Proof. exact (MK_COMB (@lem5104557 A) (@lem5104556 A _66533)). Qed.
Lemma lem5104559 {A : Type'} (_66533 : type418 A) : ((term424 A _66533) = (term425 A _66533)) = ((term419 A _66533) = (term435 A _66533)).
Proof. exact (MK_COMB (@lem5104552 A _66533) (@lem5104558 A _66533)). Qed.
Lemma lem5104560 {A : Type'} (_66533 : type418 A) : (term419 A _66533) = (term435 A _66533).
Proof. exact (EQ_MP (@lem5104559 A _66533) (@lem5104544 A _66533)). Qed.
Lemma lem5104561 {A : Type'} (_66533 : type418 A) : (term327 A _66533) = (term435 A _66533).
Proof. exact (TRANS (@lem5104540 A _66533) (@lem5104560 A _66533)). Qed.
Lemma lem5104562 {A : Type'} (_66533 : type418 A) : (term259 A _66533) = (term435 A _66533).
Proof. exact (TRANS (@lem5104416 A _66533) (@lem5104561 A _66533)). Qed.
Lemma lem5104563 {A : Type'} (_66533 : type418 A) : (term228 A _66533) = (term435 A _66533).
Proof. exact (TRANS (@lem5103983 A _66533) (@lem5104562 A _66533)). Qed.
Lemma lem5104564 {A : Type'} (_66533 : type418 A) (h1 : term228 A _66533) : term435 A _66533.
Proof. exact (EQ_MP (@lem5104563 A _66533) (@lem5103937 A _66533 h1)). Qed.
Lemma lem5104584 {A : Type'} (x : A) (lt2 : type1402 A) (y : A) (z : A) : (term436 A x lt2 y z) = (term437 A x lt2 y z).
Proof. exact (@lem17045 (lt2 x y) (lt2 y z)). Qed.
Lemma lem5104585 {A : Type'} (lt2 : type1402 A) (x : A) (z : A) : (lt2 x z) = (lt2 x z).
Proof. exact (eq_refl (lt2 x z)). Qed.
Lemma lem5104586 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5104587 {A : Type'} (x : A) (lt2 : type1402 A) (y : A) (z : A) : (term438 A x lt2 y z) = (term439 A x lt2 y z).
Proof. exact (MK_COMB (@lem5104586) (@lem5104584 A x lt2 y z)). Qed.
Lemma lem5104588 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term440 A y lt2 x z) = (term441 A y lt2 x z).
Proof. exact (MK_COMB (@lem5104587 A x lt2 y z) (@lem5104585 A lt2 x z)). Qed.
Lemma lem5104589 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term157 A y lt2 x z) = (term440 A y lt2 x z).
Proof. exact (@lem17265 (term442 A x lt2 y z) (lt2 x z)). Qed.
Lemma lem5104590 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term157 A y lt2 x z) = (term441 A y lt2 x z).
Proof. exact (TRANS (@lem5104589 A y lt2 x z) (@lem5104588 A y lt2 x z)). Qed.
Lemma lem5104591 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term158 A y lt2 x) = (term443 A y lt2 x).
Proof. exact (fun_ext (fun z : A => @lem5104590 A y lt2 x z)). Qed.
Lemma lem5104592 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104593 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term159 A y lt2 x) = (term444 A y lt2 x).
Proof. exact (MK_COMB (@lem5104592 A) (@lem5104591 A y lt2 x)). Qed.
Lemma lem5104594 {A : Type'} (lt2 : type1402 A) (x : A) : (term160 A lt2 x) = (term445 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5104593 A y lt2 x)). Qed.
Lemma lem5104595 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104596 {A : Type'} (lt2 : type1402 A) (x : A) : (term161 A lt2 x) = (term446 A lt2 x).
Proof. exact (MK_COMB (@lem5104595 A) (@lem5104594 A lt2 x)). Qed.
Lemma lem5104597 {A : Type'} (lt2 : type1402 A) : (term162 A lt2) = (term447 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5104596 A lt2 x)). Qed.
Lemma lem5104598 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104659 {A : Type'} (lt2 : type1402 A) : (term58 A lt2) = (term448 A lt2).
Proof. exact (MK_COMB (@lem5104598 A) (@lem5104597 A lt2)). Qed.
Lemma lem5104660 {A : Type'} (lt2 : type1402 A) (h1 : term58 A lt2) : term448 A lt2.
Proof. exact (EQ_MP (@lem5104659 A lt2) (@lem5103939 A lt2 h1)). Qed.
Lemma lem5104674 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term94 A lt2 s n) = (term94 A lt2 s n).
Proof. exact (eq_refl (term94 A lt2 s n)). Qed.
Lemma lem5104675 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term96 A lt2 s) = (term96 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5104674 A lt2 s n)). Qed.
Lemma lem5104676 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5104685 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term61 A lt2 s) = (term61 A lt2 s).
Proof. exact (MK_COMB (@lem5104676) (@lem5104675 A lt2 s)). Qed.
Lemma lem5104686 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term61 A lt2 s) : term61 A lt2 s.
Proof. exact (EQ_MP (@lem5104685 A lt2 s) (@lem5103941 A lt2 s h1)). Qed.
Lemma lem5104697 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term449 A y lt2 z s x) = (term450 A y lt2 z s x).
Proof. exact (@lem17362 (term73 A x lt2 z s y) (term69 A lt2 z s x)). Qed.
Lemma lem5104698 (P : nat -> Prop) : (term451 P) = (term452 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5104699 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term453 A y lt2 s x) = (term454 A y lt2 s x).
Proof. exact (@lem5104698 (term79 A y lt2 s x)). Qed.
Lemma lem5104700 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term455 A y lt2 s x z) = (term77 A y lt2 z s x).
Proof. exact (eq_refl (term455 A y lt2 s x z)). Qed.
Lemma lem5104701 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5104702 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term456 A y lt2 s x z) = (term449 A y lt2 z s x).
Proof. exact (MK_COMB (@lem5104701) (@lem5104700 A y lt2 z s x)). Qed.
Lemma lem5104703 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (x : nat) : (term456 A y lt2 s x z) = (term450 A y lt2 z s x).
Proof. exact (TRANS (@lem5104702 A y lt2 z s x) (@lem5104697 A y lt2 z s x)). Qed.
Lemma lem5104704 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term457 A y lt2 s x) = (term458 A y lt2 s x).
Proof. exact (fun_ext (fun z : nat => @lem5104703 A y lt2 z s x)). Qed.
Lemma lem5104705 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5104706 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term454 A y lt2 s x) = (term459 A y lt2 s x).
Proof. exact (MK_COMB (@lem5104705) (@lem5104704 A y lt2 s x)). Qed.
Lemma lem5104707 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term453 A y lt2 s x) = (term459 A y lt2 s x).
Proof. exact (TRANS (@lem5104699 A y lt2 s x) (@lem5104706 A y lt2 s x)). Qed.
Lemma lem5104708 (P : nat -> Prop) : (term451 P) = (term452 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5104709 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term460 A lt2 s x) = (term461 A lt2 s x).
Proof. exact (@lem5104708 (term83 A lt2 s x)). Qed.
Lemma lem5104710 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term462 A lt2 s x y) = (term81 A y lt2 s x).
Proof. exact (eq_refl (term462 A lt2 s x y)). Qed.
Lemma lem5104711 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5104712 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term463 A lt2 s x y) = (term453 A y lt2 s x).
Proof. exact (MK_COMB (@lem5104711) (@lem5104710 A y lt2 s x)). Qed.
Lemma lem5104713 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term463 A lt2 s x y) = (term459 A y lt2 s x).
Proof. exact (TRANS (@lem5104712 A y lt2 s x) (@lem5104707 A y lt2 s x)). Qed.
Lemma lem5104714 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term464 A lt2 s x) = (term465 A lt2 s x).
Proof. exact (fun_ext (fun y : nat => @lem5104713 A y lt2 s x)). Qed.
Lemma lem5104715 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5104716 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term461 A lt2 s x) = (term466 A lt2 s x).
Proof. exact (MK_COMB (@lem5104715) (@lem5104714 A lt2 s x)). Qed.
Lemma lem5104717 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term460 A lt2 s x) = (term466 A lt2 s x).
Proof. exact (TRANS (@lem5104709 A lt2 s x) (@lem5104716 A lt2 s x)). Qed.
Lemma lem5104718 (P : nat -> Prop) : (term451 P) = (term452 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5104719 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term467 A lt2 s) = (term468 A lt2 s).
Proof. exact (@lem5104718 (term87 A lt2 s)). Qed.
Lemma lem5104720 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term469 A lt2 s x) = (term85 A lt2 s x).
Proof. exact (eq_refl (term469 A lt2 s x)). Qed.
Lemma lem5104721 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5104722 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term470 A lt2 s x) = (term460 A lt2 s x).
Proof. exact (MK_COMB (@lem5104721) (@lem5104720 A lt2 s x)). Qed.
Lemma lem5104723 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term470 A lt2 s x) = (term466 A lt2 s x).
Proof. exact (TRANS (@lem5104722 A lt2 s x) (@lem5104717 A lt2 s x)). Qed.
Lemma lem5104724 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term471 A lt2 s) = (term472 A lt2 s).
Proof. exact (fun_ext (fun x : nat => @lem5104723 A lt2 s x)). Qed.
Lemma lem5104725 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5104726 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term468 A lt2 s) = (term473 A lt2 s).
Proof. exact (MK_COMB (@lem5104725) (@lem5104724 A lt2 s)). Qed.
Lemma lem5104727 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term467 A lt2 s) = (term473 A lt2 s).
Proof. exact (TRANS (@lem5104719 A lt2 s) (@lem5104726 A lt2 s)). Qed.
Lemma lem5104729 (P : nat -> Prop) : (term451 P) = (term452 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5104730 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term474 A lt2 s) = (term475 A lt2 s).
Proof. exact (@lem5104729 (term96 A lt2 s)). Qed.
Lemma lem5104731 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term476 A lt2 s n) = (term94 A lt2 s n).
Proof. exact (eq_refl (term476 A lt2 s n)). Qed.
Lemma lem5104732 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5104734 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term477 A lt2 s n) = (term478 A lt2 s n).
Proof. exact (MK_COMB (@lem5104732) (@lem5104731 A lt2 s n)). Qed.
Lemma lem5104735 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term479 A lt2 s) = (term480 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5104734 A lt2 s n)). Qed.
Lemma lem5104736 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5104737 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term475 A lt2 s) = (term481 A lt2 s).
Proof. exact (MK_COMB (@lem5104736) (@lem5104735 A lt2 s)). Qed.
Lemma lem5104738 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term474 A lt2 s) = (term481 A lt2 s).
Proof. exact (TRANS (@lem5104730 A lt2 s) (@lem5104737 A lt2 s)). Qed.
Lemma lem5104739 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5104740 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term482 A lt2 s) = (term483 A lt2 s).
Proof. exact (MK_COMB (@lem5104739) (@lem5104727 A lt2 s)). Qed.
Lemma lem5104741 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term484 A lt2 s) = (term485 A lt2 s).
Proof. exact (MK_COMB (@lem5104740 A lt2 s) (@lem5104738 A lt2 s)). Qed.
Lemma lem5104742 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term115 A lt2 s) = (term484 A lt2 s).
Proof. exact (@lem17045 (term89 A lt2 s) (term61 A lt2 s)). Qed.
Lemma lem5104743 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term115 A lt2 s) = (term485 A lt2 s).
Proof. exact (TRANS (@lem5104742 A lt2 s) (@lem5104741 A lt2 s)). Qed.
Lemma lem5104806 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term486 A P Q) = (term487 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5104807 (P : nat -> Prop) (Q : nat -> Prop) : (term488 P Q) = (term489 P Q).
Proof. exact (@lem5104806 nat P Q). Qed.
Lemma lem5104808 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term490 A lt2 s) = (term491 A lt2 s).
Proof. exact (@lem5104807 (term472 A lt2 s) (term480 A lt2 s)). Qed.
Lemma lem5104809 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term492 A lt2 s n) = (term466 A lt2 s n).
Proof. exact (eq_refl (term492 A lt2 s n)). Qed.
Lemma lem5104810 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term493 A lt2 s) = (term472 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5104809 A lt2 s n)). Qed.
Lemma lem5104811 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5104812 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term494 A lt2 s) = (term473 A lt2 s).
Proof. exact (MK_COMB (@lem5104811) (@lem5104810 A lt2 s)). Qed.
Lemma lem5104813 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5104814 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term495 A lt2 s) = (term483 A lt2 s).
Proof. exact (MK_COMB (@lem5104813) (@lem5104812 A lt2 s)). Qed.
Lemma lem5104815 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term496 A lt2 s n) = (term478 A lt2 s n).
Proof. exact (eq_refl (term496 A lt2 s n)). Qed.
Lemma lem5104816 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term497 A lt2 s) = (term480 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5104815 A lt2 s n)). Qed.
Lemma lem5104817 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5104818 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term498 A lt2 s) = (term481 A lt2 s).
Proof. exact (MK_COMB (@lem5104817) (@lem5104816 A lt2 s)). Qed.
Lemma lem5104819 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term490 A lt2 s) = (term485 A lt2 s).
Proof. exact (MK_COMB (@lem5104814 A lt2 s) (@lem5104818 A lt2 s)). Qed.
Lemma lem5104820 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5104821 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term499 A lt2 s) = (term500 A lt2 s).
Proof. exact (MK_COMB (@lem5104820) (@lem5104819 A lt2 s)). Qed.
Lemma lem5104822 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term492 A lt2 s n) = (term466 A lt2 s n).
Proof. exact (eq_refl (term492 A lt2 s n)). Qed.
Lemma lem5104823 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5104824 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term501 A lt2 s n) = (term502 A lt2 s n).
Proof. exact (MK_COMB (@lem5104823) (@lem5104822 A lt2 s n)). Qed.
Lemma lem5104825 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term496 A lt2 s n) = (term478 A lt2 s n).
Proof. exact (eq_refl (term496 A lt2 s n)). Qed.
Lemma lem5104826 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term503 A lt2 s n) = (term504 A lt2 s n).
Proof. exact (MK_COMB (@lem5104824 A lt2 s n) (@lem5104825 A lt2 s n)). Qed.
Lemma lem5104827 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term505 A lt2 s) = (term506 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5104826 A lt2 s n)). Qed.
Lemma lem5104828 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5104829 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term491 A lt2 s) = (term507 A lt2 s).
Proof. exact (MK_COMB (@lem5104828) (@lem5104827 A lt2 s)). Qed.
Lemma lem5104830 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : ((term490 A lt2 s) = (term491 A lt2 s)) = ((term485 A lt2 s) = (term507 A lt2 s)).
Proof. exact (MK_COMB (@lem5104821 A lt2 s) (@lem5104829 A lt2 s)). Qed.
Lemma lem5104831 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term485 A lt2 s) = (term507 A lt2 s).
Proof. exact (EQ_MP (@lem5104830 A lt2 s) (@lem5104808 A lt2 s)). Qed.
Lemma lem5104834 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term508 A lt2 s) = (term508 A lt2 s).
Proof. exact (eq_refl (term508 A lt2 s)). Qed.
Lemma lem5104835 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term508 A lt2 s) = ((term485 A lt2 s) = (term507 A lt2 s)).
Proof. exact (eq_refl (term508 A lt2 s)). Qed.
Lemma lem5104836 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term509 A lt2 s) = (term509 A lt2 s).
Proof. exact (eq_refl (term509 A lt2 s)). Qed.
Lemma lem5104837 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : ((term508 A lt2 s) = (term508 A lt2 s)) = ((term508 A lt2 s) = ((term485 A lt2 s) = (term507 A lt2 s))).
Proof. exact (MK_COMB (@lem5104836 A lt2 s) (@lem5104835 A lt2 s)). Qed.
Lemma lem5104838 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term508 A lt2 s) = ((term485 A lt2 s) = (term507 A lt2 s)).
Proof. exact (eq_refl (term508 A lt2 s)). Qed.
Lemma lem5104839 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5104840 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term509 A lt2 s) = (term510 A lt2 s).
Proof. exact (MK_COMB (@lem5104839) (@lem5104838 A lt2 s)). Qed.
Lemma lem5104841 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : ((term485 A lt2 s) = (term507 A lt2 s)) = ((term485 A lt2 s) = (term507 A lt2 s)).
Proof. exact (eq_refl ((term485 A lt2 s) = (term507 A lt2 s))). Qed.
Lemma lem5104842 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : ((term508 A lt2 s) = ((term485 A lt2 s) = (term507 A lt2 s))) = (((term485 A lt2 s) = (term507 A lt2 s)) = ((term485 A lt2 s) = (term507 A lt2 s))).
Proof. exact (MK_COMB (@lem5104840 A lt2 s) (@lem5104841 A lt2 s)). Qed.
Lemma lem5104843 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : ((term508 A lt2 s) = (term508 A lt2 s)) = (((term485 A lt2 s) = (term507 A lt2 s)) = ((term485 A lt2 s) = (term507 A lt2 s))).
Proof. exact (TRANS (@lem5104837 A lt2 s) (@lem5104842 A lt2 s)). Qed.
Lemma lem5104844 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : ((term485 A lt2 s) = (term507 A lt2 s)) = ((term485 A lt2 s) = (term507 A lt2 s)).
Proof. exact (EQ_MP (@lem5104843 A lt2 s) (@lem5104834 A lt2 s)). Qed.
Lemma lem5104845 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term485 A lt2 s) = (term507 A lt2 s).
Proof. exact (EQ_MP (@lem5104844 A lt2 s) (@lem5104831 A lt2 s)). Qed.
Lemma lem5104847 {A : Type'} (P : A -> Prop) (Q : Prop) : (term511 A P Q) = (term512 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5104848 (P : nat -> Prop) (Q : Prop) : (term513 P Q) = (term514 P Q).
Proof. exact (@lem5104847 nat P Q). Qed.
Lemma lem5104849 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term515 A lt2 s n) = (term516 A lt2 s n).
Proof. exact (@lem5104848 (term465 A lt2 s n) (term478 A lt2 s n)). Qed.
Lemma lem5104850 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term517 A lt2 s n y) = (term459 A y lt2 s n).
Proof. exact (eq_refl (term517 A lt2 s n y)). Qed.
Lemma lem5104851 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term518 A lt2 s n) = (term465 A lt2 s n).
Proof. exact (fun_ext (fun y : nat => @lem5104850 A y lt2 s n)). Qed.
Lemma lem5104852 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5104853 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term519 A lt2 s n) = (term466 A lt2 s n).
Proof. exact (MK_COMB (@lem5104852) (@lem5104851 A lt2 s n)). Qed.
Lemma lem5104854 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5104855 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term520 A lt2 s n) = (term502 A lt2 s n).
Proof. exact (MK_COMB (@lem5104854) (@lem5104853 A lt2 s n)). Qed.
Lemma lem5104856 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term478 A lt2 s n) = (term478 A lt2 s n).
Proof. exact (eq_refl (term478 A lt2 s n)). Qed.
Lemma lem5104857 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term515 A lt2 s n) = (term504 A lt2 s n).
Proof. exact (MK_COMB (@lem5104855 A lt2 s n) (@lem5104856 A lt2 s n)). Qed.
Lemma lem5104858 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5104859 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term521 A lt2 s n) = (term522 A lt2 s n).
Proof. exact (MK_COMB (@lem5104858) (@lem5104857 A lt2 s n)). Qed.
Lemma lem5104860 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term517 A lt2 s n y) = (term459 A y lt2 s n).
Proof. exact (eq_refl (term517 A lt2 s n y)). Qed.
Lemma lem5104861 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5104862 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term523 A lt2 s n y) = (term524 A y lt2 s n).
Proof. exact (MK_COMB (@lem5104861) (@lem5104860 A y lt2 s n)). Qed.
Lemma lem5104863 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term478 A lt2 s n) = (term478 A lt2 s n).
Proof. exact (eq_refl (term478 A lt2 s n)). Qed.
Lemma lem5104864 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term525 A y lt2 s n) = (term526 A y lt2 s n).
Proof. exact (MK_COMB (@lem5104862 A y lt2 s n) (@lem5104863 A lt2 s n)). Qed.
Lemma lem5104865 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term527 A lt2 s n) = (term528 A lt2 s n).
Proof. exact (fun_ext (fun y : nat => @lem5104864 A y lt2 s n)). Qed.
Lemma lem5104866 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5104867 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term516 A lt2 s n) = (term529 A lt2 s n).
Proof. exact (MK_COMB (@lem5104866) (@lem5104865 A lt2 s n)). Qed.
Lemma lem5104868 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : ((term515 A lt2 s n) = (term516 A lt2 s n)) = ((term504 A lt2 s n) = (term529 A lt2 s n)).
Proof. exact (MK_COMB (@lem5104859 A lt2 s n) (@lem5104867 A lt2 s n)). Qed.
Lemma lem5104869 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term504 A lt2 s n) = (term529 A lt2 s n).
Proof. exact (EQ_MP (@lem5104868 A lt2 s n) (@lem5104849 A lt2 s n)). Qed.
Lemma lem5104871 {A : Type'} (P : A -> Prop) (Q : Prop) : (term511 A P Q) = (term512 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5104872 (P : nat -> Prop) (Q : Prop) : (term513 P Q) = (term514 P Q).
Proof. exact (@lem5104871 nat P Q). Qed.
Lemma lem5104873 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term530 A y lt2 s n) = (term531 A y lt2 s n).
Proof. exact (@lem5104872 (term458 A y lt2 s n) (term478 A lt2 s n)). Qed.
Lemma lem5104874 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) : (term532 A y lt2 s n z) = (term450 A y lt2 z s n).
Proof. exact (eq_refl (term532 A y lt2 s n z)). Qed.
Lemma lem5104875 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term533 A y lt2 s n) = (term458 A y lt2 s n).
Proof. exact (fun_ext (fun z : nat => @lem5104874 A y lt2 z s n)). Qed.
Lemma lem5104876 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5104877 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term534 A y lt2 s n) = (term459 A y lt2 s n).
Proof. exact (MK_COMB (@lem5104876) (@lem5104875 A y lt2 s n)). Qed.
Lemma lem5104878 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5104879 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term535 A y lt2 s n) = (term524 A y lt2 s n).
Proof. exact (MK_COMB (@lem5104878) (@lem5104877 A y lt2 s n)). Qed.
Lemma lem5104880 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term478 A lt2 s n) = (term478 A lt2 s n).
Proof. exact (eq_refl (term478 A lt2 s n)). Qed.
Lemma lem5104881 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term530 A y lt2 s n) = (term526 A y lt2 s n).
Proof. exact (MK_COMB (@lem5104879 A y lt2 s n) (@lem5104880 A lt2 s n)). Qed.
Lemma lem5104882 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5104883 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term536 A y lt2 s n) = (term537 A y lt2 s n).
Proof. exact (MK_COMB (@lem5104882) (@lem5104881 A y lt2 s n)). Qed.
Lemma lem5104884 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) : (term532 A y lt2 s n z) = (term450 A y lt2 z s n).
Proof. exact (eq_refl (term532 A y lt2 s n z)). Qed.
Lemma lem5104885 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5104886 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) : (term538 A y lt2 s n z) = (term539 A y lt2 z s n).
Proof. exact (MK_COMB (@lem5104885) (@lem5104884 A y lt2 z s n)). Qed.
Lemma lem5104887 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term478 A lt2 s n) = (term478 A lt2 s n).
Proof. exact (eq_refl (term478 A lt2 s n)). Qed.
Lemma lem5104888 {A : Type'} (y : nat) (z : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term540 A y z lt2 s n) = (term541 A y z lt2 s n).
Proof. exact (MK_COMB (@lem5104886 A y lt2 z s n) (@lem5104887 A lt2 s n)). Qed.
Lemma lem5104889 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term542 A y lt2 s n) = (term543 A y lt2 s n).
Proof. exact (fun_ext (fun z : nat => @lem5104888 A y z lt2 s n)). Qed.
Lemma lem5104890 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5104891 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term531 A y lt2 s n) = (term544 A y lt2 s n).
Proof. exact (MK_COMB (@lem5104890) (@lem5104889 A y lt2 s n)). Qed.
Lemma lem5104892 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) : ((term530 A y lt2 s n) = (term531 A y lt2 s n)) = ((term526 A y lt2 s n) = (term544 A y lt2 s n)).
Proof. exact (MK_COMB (@lem5104883 A y lt2 s n) (@lem5104891 A y lt2 s n)). Qed.
Lemma lem5104893 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term526 A y lt2 s n) = (term544 A y lt2 s n).
Proof. exact (EQ_MP (@lem5104892 A y lt2 s n) (@lem5104873 A y lt2 s n)). Qed.
Lemma lem5104894 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term528 A lt2 s n) = (term545 A lt2 s n).
Proof. exact (fun_ext (fun y : nat => @lem5104893 A y lt2 s n)). Qed.
Lemma lem5104895 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5104896 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term529 A lt2 s n) = (term546 A lt2 s n).
Proof. exact (MK_COMB (@lem5104895) (@lem5104894 A lt2 s n)). Qed.
Lemma lem5104897 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term504 A lt2 s n) = (term546 A lt2 s n).
Proof. exact (TRANS (@lem5104869 A lt2 s n) (@lem5104896 A lt2 s n)). Qed.
Lemma lem5104898 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term506 A lt2 s) = (term547 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5104897 A lt2 s n)). Qed.
Lemma lem5104899 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5104900 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term507 A lt2 s) = (term548 A lt2 s).
Proof. exact (MK_COMB (@lem5104899) (@lem5104898 A lt2 s)). Qed.
Lemma lem5104902 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term485 A lt2 s) = (term548 A lt2 s).
Proof. exact (TRANS (@lem5104845 A lt2 s) (@lem5104900 A lt2 s)). Qed.
Lemma lem5104903 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term115 A lt2 s) = (term548 A lt2 s).
Proof. exact (TRANS (@lem5104743 A lt2 s) (@lem5104902 A lt2 s)). Qed.
Lemma lem5104904 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term115 A lt2 s) : term548 A lt2 s.
Proof. exact (EQ_MP (@lem5104903 A lt2 s) (@lem5103946 A lt2 s h1)). Qed.
Lemma lem5104905 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term546 A lt2 s n) : term546 A lt2 s n.
Proof. exact (h1). Qed.
Lemma lem5104906 {A : Type'} (y : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term544 A y lt2 s n) : term544 A y lt2 s n.
Proof. exact (h1). Qed.
Lemma lem5104907 {A : Type'} (y : nat) (z : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term541 A y z lt2 s n) : term541 A y z lt2 s n.
Proof. exact (h1). Qed.
Lemma lem5104938 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5104939 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5104938 A (A -> Prop) f x). Qed.
Lemma lem5104940 {A : Type'} (lt2 : type1402 A) (x : A) : (lt2 x) = (@I (A -> A -> Prop) lt2 x).
Proof. exact (@lem5104939 A lt2 x). Qed.
Lemma lem5104941 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5104942 {A : Type'} (lt2 : type1402 A) (x : A) (z : A) : (lt2 x z) = (@I (A -> A -> Prop) lt2 x z).
Proof. exact (MK_COMB (@lem5104940 A lt2 x) (@lem5104941 A z)). Qed.
Lemma lem5104944 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5104945 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5104944 A Prop f x). Qed.
Lemma lem5104946 {A : Type'} (lt2 : type1402 A) (x : A) (z : A) : (@I (A -> A -> Prop) lt2 x z) = (term549 A lt2 x z).
Proof. exact (@lem5104945 A (@I (A -> A -> Prop) lt2 x) z). Qed.
Lemma lem5104948 {A : Type'} (lt2 : type1402 A) (x : A) (z : A) : (lt2 x z) = (term549 A lt2 x z).
Proof. exact (TRANS (@lem5104942 A lt2 x z) (@lem5104946 A lt2 x z)). Qed.
Lemma lem5104949 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5104956 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5104957 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5104956 A (A -> Prop) f x). Qed.
Lemma lem5104958 {A : Type'} (lt2 : type1402 A) (y : A) : (lt2 y) = (@I (A -> A -> Prop) lt2 y).
Proof. exact (@lem5104957 A lt2 y). Qed.
Lemma lem5104959 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5104960 {A : Type'} (lt2 : type1402 A) (y : A) (z : A) : (lt2 y z) = (@I (A -> A -> Prop) lt2 y z).
Proof. exact (MK_COMB (@lem5104958 A lt2 y) (@lem5104959 A z)). Qed.
Lemma lem5104962 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5104963 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5104962 A Prop f x). Qed.
Lemma lem5104964 {A : Type'} (lt2 : type1402 A) (y : A) (z : A) : (@I (A -> A -> Prop) lt2 y z) = (term549 A lt2 y z).
Proof. exact (@lem5104963 A (@I (A -> A -> Prop) lt2 y) z). Qed.
Lemma lem5104966 {A : Type'} (lt2 : type1402 A) (y : A) (z : A) : (lt2 y z) = (term549 A lt2 y z).
Proof. exact (TRANS (@lem5104960 A lt2 y z) (@lem5104964 A lt2 y z)). Qed.
Lemma lem5104967 {A : Type'} (lt2 : type1402 A) (y : A) (z : A) : (term550 A lt2 y z) = (term551 A lt2 y z).
Proof. exact (MK_COMB (@lem5104949) (@lem5104966 A lt2 y z)). Qed.
Lemma lem5104968 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5104975 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5104976 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5104975 A (A -> Prop) f x). Qed.
Lemma lem5104977 {A : Type'} (lt2 : type1402 A) (x : A) : (lt2 x) = (@I (A -> A -> Prop) lt2 x).
Proof. exact (@lem5104976 A lt2 x). Qed.
Lemma lem5104978 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5104979 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (lt2 x y) = (@I (A -> A -> Prop) lt2 x y).
Proof. exact (MK_COMB (@lem5104977 A lt2 x) (@lem5104978 A y)). Qed.
Lemma lem5104981 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5104982 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5104981 A Prop f x). Qed.
Lemma lem5104983 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) lt2 x y) = (term549 A lt2 x y).
Proof. exact (@lem5104982 A (@I (A -> A -> Prop) lt2 x) y). Qed.
Lemma lem5104985 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (lt2 x y) = (term549 A lt2 x y).
Proof. exact (TRANS (@lem5104979 A lt2 x y) (@lem5104983 A lt2 x y)). Qed.
Lemma lem5104986 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term550 A lt2 x y) = (term551 A lt2 x y).
Proof. exact (MK_COMB (@lem5104968) (@lem5104985 A lt2 x y)). Qed.
Lemma lem5104987 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5104988 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term552 A lt2 x y) = (term553 A lt2 x y).
Proof. exact (MK_COMB (@lem5104987) (@lem5104986 A lt2 x y)). Qed.
Lemma lem5104989 {A : Type'} (x : A) (lt2 : type1402 A) (y : A) (z : A) : (term437 A x lt2 y z) = (term554 A x lt2 y z).
Proof. exact (MK_COMB (@lem5104988 A lt2 x y) (@lem5104967 A lt2 y z)). Qed.
Lemma lem5104990 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5104991 {A : Type'} (x : A) (lt2 : type1402 A) (y : A) (z : A) : (term439 A x lt2 y z) = (term555 A x lt2 y z).
Proof. exact (MK_COMB (@lem5104990) (@lem5104989 A x lt2 y z)). Qed.
Lemma lem5104992 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term441 A y lt2 x z) = (term556 A y lt2 x z).
Proof. exact (MK_COMB (@lem5104991 A x lt2 y z) (@lem5104948 A lt2 x z)). Qed.
Lemma lem5104993 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term443 A y lt2 x) = (term557 A y lt2 x).
Proof. exact (fun_ext (fun z : A => @lem5104992 A y lt2 x z)). Qed.
Lemma lem5104994 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104995 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term444 A y lt2 x) = (term558 A y lt2 x).
Proof. exact (MK_COMB (@lem5104994 A) (@lem5104993 A y lt2 x)). Qed.
Lemma lem5104996 {A : Type'} (lt2 : type1402 A) (x : A) : (term445 A lt2 x) = (term559 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5104995 A y lt2 x)). Qed.
Lemma lem5104997 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5104998 {A : Type'} (lt2 : type1402 A) (x : A) : (term446 A lt2 x) = (term560 A lt2 x).
Proof. exact (MK_COMB (@lem5104997 A) (@lem5104996 A lt2 x)). Qed.
Lemma lem5104999 {A : Type'} (lt2 : type1402 A) : (term447 A lt2) = (term561 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5104998 A lt2 x)). Qed.
Lemma lem5105000 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5105001 {A : Type'} (lt2 : type1402 A) : (term448 A lt2) = (term562 A lt2).
Proof. exact (MK_COMB (@lem5105000 A) (@lem5104999 A lt2)). Qed.
Lemma lem5105002 {A : Type'} (lt2 : type1402 A) (h1 : term58 A lt2) : term562 A lt2.
Proof. exact (EQ_MP (@lem5105001 A lt2) (@lem5104660 A lt2 h1)). Qed.
Lemma lem5105038 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem5105039 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5105044 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105045 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5105044 nat nat f x). Qed.
Lemma lem5105047 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem5105045 S n). Qed.
Lemma lem5105048 {A : Type'} (s : nat -> A) (n : nat) : (term563 A s n) = (term564 A s n).
Proof. exact (MK_COMB (@lem5105039 A s) (@lem5105047 n)). Qed.
Lemma lem5105050 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105051 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5105050 nat A f x). Qed.
Lemma lem5105052 {A : Type'} (s : nat -> A) (n : nat) : (term564 A s n) = (term565 A s n).
Proof. exact (@lem5105051 A s (@I (nat -> nat) S n)). Qed.
Lemma lem5105053 {A : Type'} (s : nat -> A) (n : nat) : (term563 A s n) = (term565 A s n).
Proof. exact (TRANS (@lem5105048 A s n) (@lem5105052 A s n)). Qed.
Lemma lem5105058 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105059 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5105058 nat A f x). Qed.
Lemma lem5105061 {A : Type'} (s : nat -> A) (n : nat) : (s n) = (@I (nat -> A) s n).
Proof. exact (@lem5105059 A s n). Qed.
Lemma lem5105062 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term566 A lt2 s n) = (term567 A lt2 s n).
Proof. exact (MK_COMB (@lem5105038 A lt2) (@lem5105053 A s n)). Qed.
Lemma lem5105063 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term94 A lt2 s n) = (term568 A lt2 s n).
Proof. exact (MK_COMB (@lem5105062 A lt2 s n) (@lem5105061 A s n)). Qed.
Lemma lem5105065 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105066 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5105065 A (A -> Prop) f x). Qed.
Lemma lem5105067 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term567 A lt2 s n) = (term569 A lt2 s n).
Proof. exact (@lem5105066 A lt2 (term565 A s n)). Qed.
Lemma lem5105068 {A : Type'} (s : nat -> A) (n : nat) : (@I (nat -> A) s n) = (@I (nat -> A) s n).
Proof. exact (eq_refl (@I (nat -> A) s n)). Qed.
Lemma lem5105069 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term568 A lt2 s n) = (term570 A lt2 s n).
Proof. exact (MK_COMB (@lem5105067 A lt2 s n) (@lem5105068 A s n)). Qed.
Lemma lem5105071 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105072 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5105071 A Prop f x). Qed.
Lemma lem5105073 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term570 A lt2 s n) = (term571 A lt2 s n).
Proof. exact (@lem5105072 A (term569 A lt2 s n) (@I (nat -> A) s n)). Qed.
Lemma lem5105074 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term568 A lt2 s n) = (term571 A lt2 s n).
Proof. exact (TRANS (@lem5105069 A lt2 s n) (@lem5105073 A lt2 s n)). Qed.
Lemma lem5105075 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term94 A lt2 s n) = (term571 A lt2 s n).
Proof. exact (TRANS (@lem5105063 A lt2 s n) (@lem5105074 A lt2 s n)). Qed.
Lemma lem5105076 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term96 A lt2 s) = (term572 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5105075 A lt2 s n)). Qed.
Lemma lem5105077 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5105078 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term61 A lt2 s) = (term573 A lt2 s).
Proof. exact (MK_COMB (@lem5105077) (@lem5105076 A lt2 s)). Qed.
Lemma lem5105079 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term61 A lt2 s) : term573 A lt2 s.
Proof. exact (EQ_MP (@lem5105078 A lt2 s) (@lem5104686 A lt2 s h1)). Qed.
Lemma lem5105080 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5105081 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem5105082 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5105087 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105088 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5105087 nat nat f x). Qed.
Lemma lem5105090 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem5105088 S n). Qed.
Lemma lem5105091 {A : Type'} (s : nat -> A) (n : nat) : (term563 A s n) = (term564 A s n).
Proof. exact (MK_COMB (@lem5105082 A s) (@lem5105090 n)). Qed.
Lemma lem5105093 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105094 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5105093 nat A f x). Qed.
Lemma lem5105095 {A : Type'} (s : nat -> A) (n : nat) : (term564 A s n) = (term565 A s n).
Proof. exact (@lem5105094 A s (@I (nat -> nat) S n)). Qed.
Lemma lem5105096 {A : Type'} (s : nat -> A) (n : nat) : (term563 A s n) = (term565 A s n).
Proof. exact (TRANS (@lem5105091 A s n) (@lem5105095 A s n)). Qed.
Lemma lem5105101 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105102 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5105101 nat A f x). Qed.
Lemma lem5105104 {A : Type'} (s : nat -> A) (n : nat) : (s n) = (@I (nat -> A) s n).
Proof. exact (@lem5105102 A s n). Qed.
Lemma lem5105105 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term566 A lt2 s n) = (term567 A lt2 s n).
Proof. exact (MK_COMB (@lem5105081 A lt2) (@lem5105096 A s n)). Qed.
Lemma lem5105106 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term94 A lt2 s n) = (term568 A lt2 s n).
Proof. exact (MK_COMB (@lem5105105 A lt2 s n) (@lem5105104 A s n)). Qed.
Lemma lem5105108 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105109 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5105108 A (A -> Prop) f x). Qed.
Lemma lem5105110 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term567 A lt2 s n) = (term569 A lt2 s n).
Proof. exact (@lem5105109 A lt2 (term565 A s n)). Qed.
Lemma lem5105111 {A : Type'} (s : nat -> A) (n : nat) : (@I (nat -> A) s n) = (@I (nat -> A) s n).
Proof. exact (eq_refl (@I (nat -> A) s n)). Qed.
Lemma lem5105112 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term568 A lt2 s n) = (term570 A lt2 s n).
Proof. exact (MK_COMB (@lem5105110 A lt2 s n) (@lem5105111 A s n)). Qed.
Lemma lem5105114 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105115 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5105114 A Prop f x). Qed.
Lemma lem5105116 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term570 A lt2 s n) = (term571 A lt2 s n).
Proof. exact (@lem5105115 A (term569 A lt2 s n) (@I (nat -> A) s n)). Qed.
Lemma lem5105117 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term568 A lt2 s n) = (term571 A lt2 s n).
Proof. exact (TRANS (@lem5105112 A lt2 s n) (@lem5105116 A lt2 s n)). Qed.
Lemma lem5105118 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term94 A lt2 s n) = (term571 A lt2 s n).
Proof. exact (TRANS (@lem5105106 A lt2 s n) (@lem5105117 A lt2 s n)). Qed.
Lemma lem5105119 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term478 A lt2 s n) = (term574 A lt2 s n).
Proof. exact (MK_COMB (@lem5105080) (@lem5105118 A lt2 s n)). Qed.
Lemma lem5105120 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5105121 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem5105126 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105127 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5105126 nat A f x). Qed.
Lemma lem5105129 {A : Type'} (s : nat -> A) (z : nat) : (s z) = (@I (nat -> A) s z).
Proof. exact (@lem5105127 A s z). Qed.
Lemma lem5105134 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105135 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5105134 nat A f x). Qed.
Lemma lem5105137 {A : Type'} (s : nat -> A) (n : nat) : (s n) = (@I (nat -> A) s n).
Proof. exact (@lem5105135 A s n). Qed.
Lemma lem5105138 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (z : nat) : (term575 A lt2 s z) = (term576 A lt2 s z).
Proof. exact (MK_COMB (@lem5105121 A lt2) (@lem5105129 A s z)). Qed.
Lemma lem5105139 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) : (term69 A lt2 z s n) = (term577 A lt2 z s n).
Proof. exact (MK_COMB (@lem5105138 A lt2 s z) (@lem5105137 A s n)). Qed.
Lemma lem5105141 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105142 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5105141 A (A -> Prop) f x). Qed.
Lemma lem5105143 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (z : nat) : (term576 A lt2 s z) = (term578 A lt2 s z).
Proof. exact (@lem5105142 A lt2 (@I (nat -> A) s z)). Qed.
Lemma lem5105144 {A : Type'} (s : nat -> A) (n : nat) : (@I (nat -> A) s n) = (@I (nat -> A) s n).
Proof. exact (eq_refl (@I (nat -> A) s n)). Qed.
Lemma lem5105145 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) : (term577 A lt2 z s n) = (term579 A lt2 z s n).
Proof. exact (MK_COMB (@lem5105143 A lt2 s z) (@lem5105144 A s n)). Qed.
Lemma lem5105147 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105148 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5105147 A Prop f x). Qed.
Lemma lem5105149 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) : (term579 A lt2 z s n) = (term580 A lt2 z s n).
Proof. exact (@lem5105148 A (term578 A lt2 s z) (@I (nat -> A) s n)). Qed.
Lemma lem5105150 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) : (term577 A lt2 z s n) = (term580 A lt2 z s n).
Proof. exact (TRANS (@lem5105145 A lt2 z s n) (@lem5105149 A lt2 z s n)). Qed.
Lemma lem5105151 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) : (term69 A lt2 z s n) = (term580 A lt2 z s n).
Proof. exact (TRANS (@lem5105139 A lt2 z s n) (@lem5105150 A lt2 z s n)). Qed.
Lemma lem5105152 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) : (term581 A lt2 z s n) = (term582 A lt2 z s n).
Proof. exact (MK_COMB (@lem5105120) (@lem5105151 A lt2 z s n)). Qed.
Lemma lem5105153 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem5105158 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105159 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5105158 nat A f x). Qed.
Lemma lem5105161 {A : Type'} (s : nat -> A) (z : nat) : (s z) = (@I (nat -> A) s z).
Proof. exact (@lem5105159 A s z). Qed.
Lemma lem5105166 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105167 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5105166 nat A f x). Qed.
Lemma lem5105169 {A : Type'} (s : nat -> A) (y : nat) : (s y) = (@I (nat -> A) s y).
Proof. exact (@lem5105167 A s y). Qed.
Lemma lem5105170 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (z : nat) : (term575 A lt2 s z) = (term576 A lt2 s z).
Proof. exact (MK_COMB (@lem5105153 A lt2) (@lem5105161 A s z)). Qed.
Lemma lem5105171 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term69 A lt2 z s y) = (term577 A lt2 z s y).
Proof. exact (MK_COMB (@lem5105170 A lt2 s z) (@lem5105169 A s y)). Qed.
Lemma lem5105173 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105174 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5105173 A (A -> Prop) f x). Qed.
Lemma lem5105175 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (z : nat) : (term576 A lt2 s z) = (term578 A lt2 s z).
Proof. exact (@lem5105174 A lt2 (@I (nat -> A) s z)). Qed.
Lemma lem5105176 {A : Type'} (s : nat -> A) (y : nat) : (@I (nat -> A) s y) = (@I (nat -> A) s y).
Proof. exact (eq_refl (@I (nat -> A) s y)). Qed.
Lemma lem5105177 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term577 A lt2 z s y) = (term579 A lt2 z s y).
Proof. exact (MK_COMB (@lem5105175 A lt2 s z) (@lem5105176 A s y)). Qed.
Lemma lem5105179 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105180 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5105179 A Prop f x). Qed.
Lemma lem5105181 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term579 A lt2 z s y) = (term580 A lt2 z s y).
Proof. exact (@lem5105180 A (term578 A lt2 s z) (@I (nat -> A) s y)). Qed.
Lemma lem5105182 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term577 A lt2 z s y) = (term580 A lt2 z s y).
Proof. exact (TRANS (@lem5105177 A lt2 z s y) (@lem5105181 A lt2 z s y)). Qed.
Lemma lem5105183 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term69 A lt2 z s y) = (term580 A lt2 z s y).
Proof. exact (TRANS (@lem5105171 A lt2 z s y) (@lem5105182 A lt2 z s y)). Qed.
Lemma lem5105184 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem5105189 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105190 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5105189 nat A f x). Qed.
Lemma lem5105192 {A : Type'} (s : nat -> A) (y : nat) : (s y) = (@I (nat -> A) s y).
Proof. exact (@lem5105190 A s y). Qed.
Lemma lem5105197 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105198 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5105197 nat A f x). Qed.
Lemma lem5105200 {A : Type'} (s : nat -> A) (n : nat) : (s n) = (@I (nat -> A) s n).
Proof. exact (@lem5105198 A s n). Qed.
Lemma lem5105201 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (y : nat) : (term575 A lt2 s y) = (term576 A lt2 s y).
Proof. exact (MK_COMB (@lem5105184 A lt2) (@lem5105192 A s y)). Qed.
Lemma lem5105202 {A : Type'} (lt2 : type1402 A) (y : nat) (s : nat -> A) (n : nat) : (term69 A lt2 y s n) = (term577 A lt2 y s n).
Proof. exact (MK_COMB (@lem5105201 A lt2 s y) (@lem5105200 A s n)). Qed.
Lemma lem5105204 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105205 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5105204 A (A -> Prop) f x). Qed.
Lemma lem5105206 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (y : nat) : (term576 A lt2 s y) = (term578 A lt2 s y).
Proof. exact (@lem5105205 A lt2 (@I (nat -> A) s y)). Qed.
Lemma lem5105207 {A : Type'} (s : nat -> A) (n : nat) : (@I (nat -> A) s n) = (@I (nat -> A) s n).
Proof. exact (eq_refl (@I (nat -> A) s n)). Qed.
Lemma lem5105208 {A : Type'} (lt2 : type1402 A) (y : nat) (s : nat -> A) (n : nat) : (term577 A lt2 y s n) = (term579 A lt2 y s n).
Proof. exact (MK_COMB (@lem5105206 A lt2 s y) (@lem5105207 A s n)). Qed.
Lemma lem5105210 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5105211 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5105210 A Prop f x). Qed.
Lemma lem5105212 {A : Type'} (lt2 : type1402 A) (y : nat) (s : nat -> A) (n : nat) : (term579 A lt2 y s n) = (term580 A lt2 y s n).
Proof. exact (@lem5105211 A (term578 A lt2 s y) (@I (nat -> A) s n)). Qed.
Lemma lem5105213 {A : Type'} (lt2 : type1402 A) (y : nat) (s : nat -> A) (n : nat) : (term577 A lt2 y s n) = (term580 A lt2 y s n).
Proof. exact (TRANS (@lem5105208 A lt2 y s n) (@lem5105212 A lt2 y s n)). Qed.
Lemma lem5105214 {A : Type'} (lt2 : type1402 A) (y : nat) (s : nat -> A) (n : nat) : (term69 A lt2 y s n) = (term580 A lt2 y s n).
Proof. exact (TRANS (@lem5105202 A lt2 y s n) (@lem5105213 A lt2 y s n)). Qed.
Lemma lem5105215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5105216 {A : Type'} (lt2 : type1402 A) (y : nat) (s : nat -> A) (n : nat) : (term71 A lt2 y s n) = (term583 A lt2 y s n).
Proof. exact (MK_COMB (@lem5105215) (@lem5105214 A lt2 y s n)). Qed.
Lemma lem5105217 {A : Type'} (n : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term73 A n lt2 z s y) = (term584 A n lt2 z s y).
Proof. exact (MK_COMB (@lem5105216 A lt2 y s n) (@lem5105183 A lt2 z s y)). Qed.
Lemma lem5105218 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5105219 {A : Type'} (n : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term585 A n lt2 z s y) = (term586 A n lt2 z s y).
Proof. exact (MK_COMB (@lem5105218) (@lem5105217 A n lt2 z s y)). Qed.
Lemma lem5105220 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) : (term450 A y lt2 z s n) = (term587 A y lt2 z s n).
Proof. exact (MK_COMB (@lem5105219 A n lt2 z s y) (@lem5105152 A lt2 z s n)). Qed.
Lemma lem5105221 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5105222 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) : (term539 A y lt2 z s n) = (term588 A y lt2 z s n).
Proof. exact (MK_COMB (@lem5105221) (@lem5105220 A y lt2 z s n)). Qed.
Lemma lem5105223 {A : Type'} (y : nat) (z : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term541 A y z lt2 s n) = (term589 A y z lt2 s n).
Proof. exact (MK_COMB (@lem5105222 A y lt2 z s n) (@lem5105119 A lt2 s n)). Qed.
Lemma lem5105224 {A : Type'} (y : nat) (z : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term541 A y z lt2 s n) : term589 A y z lt2 s n.
Proof. exact (EQ_MP (@lem5105223 A y z lt2 s n) (@lem5104907 A y z lt2 s n h1)). Qed.
Lemma lem5105448 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term587 A y lt2 z s n) : term587 A y lt2 z s n.
Proof. exact (h1). Qed.
Lemma lem5105451 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term587 A y lt2 z s n) : term584 A n lt2 z s y.
Proof. exact (proj1 (@lem5105448 A y lt2 z s n h1)). Qed.
Lemma lem5105474 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term556 A y lt2 x z) = (term556 A y lt2 x z).
Proof. exact (eq_refl (term556 A y lt2 x z)). Qed.
Lemma lem5105475 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term557 A y lt2 x) = (term557 A y lt2 x).
Proof. exact (fun_ext (fun z : A => @lem5105474 A y lt2 x z)). Qed.
Lemma lem5105476 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5105477 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term558 A y lt2 x) = (term558 A y lt2 x).
Proof. exact (MK_COMB (@lem5105476 A) (@lem5105475 A y lt2 x)). Qed.
Lemma lem5105478 {A : Type'} (lt2 : type1402 A) (x : A) : (term559 A lt2 x) = (term559 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5105477 A y lt2 x)). Qed.
Lemma lem5105479 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5105480 {A : Type'} (lt2 : type1402 A) (x : A) : (term560 A lt2 x) = (term560 A lt2 x).
Proof. exact (MK_COMB (@lem5105479 A) (@lem5105478 A lt2 x)). Qed.
Lemma lem5105481 {A : Type'} (lt2 : type1402 A) : (term561 A lt2) = (term561 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5105480 A lt2 x)). Qed.
Lemma lem5105482 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5105484 {A : Type'} (lt2 : type1402 A) : (term562 A lt2) = (term562 A lt2).
Proof. exact (MK_COMB (@lem5105482 A) (@lem5105481 A lt2)). Qed.
Lemma lem5105485 {A : Type'} (lt2 : type1402 A) (h1 : term58 A lt2) : term562 A lt2.
Proof. exact (EQ_MP (@lem5105484 A lt2) (@lem5105002 A lt2 h1)). Qed.
Lemma lem5105621 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term571 A lt2 s n) = (term571 A lt2 s n).
Proof. exact (eq_refl (term571 A lt2 s n)). Qed.
Lemma lem5105622 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term572 A lt2 s) = (term572 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5105621 A lt2 s n)). Qed.
Lemma lem5105623 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5105625 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term573 A lt2 s) = (term573 A lt2 s).
Proof. exact (MK_COMB (@lem5105623) (@lem5105622 A lt2 s)). Qed.
Lemma lem5105626 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term61 A lt2 s) : term573 A lt2 s.
Proof. exact (EQ_MP (@lem5105625 A lt2 s) (@lem5105079 A lt2 s h1)). Qed.
Lemma lem5105699 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term574 A lt2 s n) : term574 A lt2 s n.
Proof. exact (h1). Qed.
Lemma lem5105703 {A : Type'} (_66537 : A) (lt2 : type1402 A) (h1 : term58 A lt2) : term590 A lt2 _66537.
Proof. exact (@lem5105485 A lt2 h1 _66537). Qed.
Lemma lem5105704 {A : Type'} (lt2 : type1402 A) (_66537 : A) : (term590 A lt2 _66537) = (term560 A lt2 _66537).
Proof. exact (eq_refl (term590 A lt2 _66537)). Qed.
Lemma lem5105705 {A : Type'} (_66537 : A) (lt2 : type1402 A) (h1 : term58 A lt2) : term560 A lt2 _66537.
Proof. exact (EQ_MP (@lem5105704 A lt2 _66537) (@lem5105703 A _66537 lt2 h1)). Qed.
Lemma lem5105706 {A : Type'} (_66537 : A) (_66538 : A) (lt2 : type1402 A) (h1 : term58 A lt2) : term591 A lt2 _66537 _66538.
Proof. exact (@lem5105705 A _66537 lt2 h1 _66538). Qed.
Lemma lem5105707 {A : Type'} (_66538 : A) (lt2 : type1402 A) (_66537 : A) : (term591 A lt2 _66537 _66538) = (term558 A _66538 lt2 _66537).
Proof. exact (eq_refl (term591 A lt2 _66537 _66538)). Qed.
Lemma lem5105708 {A : Type'} (_66538 : A) (_66537 : A) (lt2 : type1402 A) (h1 : term58 A lt2) : term558 A _66538 lt2 _66537.
Proof. exact (EQ_MP (@lem5105707 A _66538 lt2 _66537) (@lem5105706 A _66537 _66538 lt2 h1)). Qed.
Lemma lem5105709 {A : Type'} (_66538 : A) (_66537 : A) (_66539 : A) (lt2 : type1402 A) (h1 : term58 A lt2) : term592 A _66538 lt2 _66537 _66539.
Proof. exact (@lem5105708 A _66538 _66537 lt2 h1 _66539). Qed.
Lemma lem5105710 {A : Type'} (_66538 : A) (lt2 : type1402 A) (_66537 : A) (_66539 : A) : (term592 A _66538 lt2 _66537 _66539) = (term556 A _66538 lt2 _66537 _66539).
Proof. exact (eq_refl (term592 A _66538 lt2 _66537 _66539)). Qed.
Lemma lem5105711 {A : Type'} (_66538 : A) (_66537 : A) (_66539 : A) (lt2 : type1402 A) (h1 : term58 A lt2) : term556 A _66538 lt2 _66537 _66539.
Proof. exact (EQ_MP (@lem5105710 A _66538 lt2 _66537 _66539) (@lem5105709 A _66538 _66537 _66539 lt2 h1)). Qed.
Lemma lem5105754 {A : Type'} (_66554 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term61 A lt2 s) : term593 A lt2 s _66554.
Proof. exact (@lem5105626 A lt2 s h1 _66554). Qed.
Lemma lem5105755 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66554 : nat) : (term593 A lt2 s _66554) = (term571 A lt2 s _66554).
Proof. exact (eq_refl (term593 A lt2 s _66554)). Qed.
Lemma lem5105790 {A : Type'} (_66538 : A) (lt2 : type1402 A) (_66537 : A) (_66539 : A) : (term556 A _66538 lt2 _66537 _66539) = (term594 A _66538 lt2 _66537 _66539).
Proof. exact (@lem5103223 (term551 A lt2 _66537 _66538) (term551 A lt2 _66538 _66539) (term549 A lt2 _66537 _66539)). Qed.
Lemma lem5105791 {A : Type'} (_66538 : A) (_66537 : A) (_66539 : A) (lt2 : type1402 A) (h1 : term58 A lt2) : term594 A _66538 lt2 _66537 _66539.
Proof. exact (EQ_MP (@lem5105790 A _66538 lt2 _66537 _66539) (@lem5105711 A _66538 _66537 _66539 lt2 h1)). Qed.
Lemma lem5105809 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term587 A y lt2 z s n) : term582 A lt2 z s n.
Proof. exact (proj2 (@lem5105448 A y lt2 z s n h1)). Qed.
Lemma lem5105845 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term574 A lt2 s n) : term574 A lt2 s n.
Proof. exact (h1). Qed.
Lemma lem5105847 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term587 A y lt2 z s n) : term580 A lt2 z s y.
Proof. exact (proj2 (@lem5105451 A y lt2 z s n h1)). Qed.
Lemma lem5105848 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term587 A y lt2 z s n) : term595 A lt2 z s y.
Proof. exact (fun h0 : term582 A lt2 z s y => @lem5105847 A y lt2 z s n h1). Qed.
Lemma lem5105850 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5105851 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (y : nat) : (term595 A lt2 z s y) = (term580 A lt2 z s y).
Proof. exact (@lem5105850 (term580 A lt2 z s y)). Qed.
Lemma lem5105852 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term587 A y lt2 z s n) : term580 A lt2 z s y.
Proof. exact (EQ_MP (@lem5105851 A lt2 z s y) (@lem5105848 A y lt2 z s n h1)). Qed.
Lemma lem5105854 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term587 A y lt2 z s n) : term580 A lt2 y s n.
Proof. exact (proj1 (@lem5105451 A y lt2 z s n h1)). Qed.
Lemma lem5105855 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term587 A y lt2 z s n) : term595 A lt2 y s n.
Proof. exact (fun h0 : term582 A lt2 y s n => @lem5105854 A y lt2 z s n h1). Qed.
Lemma lem5105857 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5105858 {A : Type'} (lt2 : type1402 A) (y : nat) (s : nat -> A) (n : nat) : (term595 A lt2 y s n) = (term580 A lt2 y s n).
Proof. exact (@lem5105857 (term580 A lt2 y s n)). Qed.
Lemma lem5105859 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term587 A y lt2 z s n) : term580 A lt2 y s n.
Proof. exact (EQ_MP (@lem5105858 A lt2 y s n) (@lem5105855 A y lt2 z s n h1)). Qed.
Lemma lem5105875 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5105876 {A : Type'} (_66537 : A) (lt2 : type1402 A) (_66538 : A) (_66539 : A) : (term597 A _66538 lt2 _66537 _66539) = (term598 A _66537 lt2 _66538 _66539).
Proof. exact (@lem5105875 (term549 A lt2 _66537 _66539) (term551 A lt2 _66538 _66539)). Qed.
Lemma lem5105882 {A : Type'} (lt2 : type1402 A) (_66537 : A) (_66538 : A) : (term553 A lt2 _66537 _66538) = (term553 A lt2 _66537 _66538).
Proof. exact (eq_refl (term553 A lt2 _66537 _66538)). Qed.
Lemma lem5105883 {A : Type'} (_66537 : A) (lt2 : type1402 A) (_66538 : A) (_66539 : A) : (term594 A _66538 lt2 _66537 _66539) = (term599 A _66537 lt2 _66538 _66539).
Proof. exact (MK_COMB (@lem5105882 A lt2 _66537 _66538) (@lem5105876 A _66537 lt2 _66538 _66539)). Qed.
Lemma lem5105887 (q : Prop) (p : Prop) (r : Prop) : (term45 p q r) = (term45 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5105888 {A : Type'} (_66537 : A) (lt2 : type1402 A) (_66538 : A) (_66539 : A) : (term599 A _66537 lt2 _66538 _66539) = (term600 A _66537 lt2 _66538 _66539).
Proof. exact (@lem5105887 (term549 A lt2 _66537 _66539) (term551 A lt2 _66537 _66538) (term551 A lt2 _66538 _66539)). Qed.
Lemma lem5105904 {A : Type'} (_66537 : A) (lt2 : type1402 A) (_66538 : A) (_66539 : A) : (term594 A _66538 lt2 _66537 _66539) = (term600 A _66537 lt2 _66538 _66539).
Proof. exact (TRANS (@lem5105883 A _66537 lt2 _66538 _66539) (@lem5105888 A _66537 lt2 _66538 _66539)). Qed.
Lemma lem5105905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5105906 {A : Type'} (_66537 : A) (lt2 : type1402 A) (_66538 : A) (_66539 : A) : (term601 A _66538 lt2 _66537 _66539) = (term602 A _66537 lt2 _66538 _66539).
Proof. exact (MK_COMB (@lem5105905) (@lem5105904 A _66537 lt2 _66538 _66539)). Qed.
Lemma lem5105922 {A : Type'} (_66537 : A) (lt2 : type1402 A) (_66538 : A) (_66539 : A) : (term600 A _66537 lt2 _66538 _66539) = (term600 A _66537 lt2 _66538 _66539).
Proof. exact (eq_refl (term600 A _66537 lt2 _66538 _66539)). Qed.
Lemma lem5105923 {A : Type'} (_66537 : A) (lt2 : type1402 A) (_66538 : A) (_66539 : A) : ((term594 A _66538 lt2 _66537 _66539) = (term600 A _66537 lt2 _66538 _66539)) = ((term600 A _66537 lt2 _66538 _66539) = (term600 A _66537 lt2 _66538 _66539)).
Proof. exact (MK_COMB (@lem5105906 A _66537 lt2 _66538 _66539) (@lem5105922 A _66537 lt2 _66538 _66539)). Qed.
Lemma lem5105925 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5105926 (x : Prop) : (x = x) = True.
Proof. exact (@lem5105925 Prop x). Qed.
Lemma lem5105927 {A : Type'} (_66537 : A) (lt2 : type1402 A) (_66538 : A) (_66539 : A) : ((term600 A _66537 lt2 _66538 _66539) = (term600 A _66537 lt2 _66538 _66539)) = True.
Proof. exact (@lem5105926 (term600 A _66537 lt2 _66538 _66539)). Qed.
Lemma lem5105928 {A : Type'} (_66537 : A) (lt2 : type1402 A) (_66538 : A) (_66539 : A) : ((term594 A _66538 lt2 _66537 _66539) = (term600 A _66537 lt2 _66538 _66539)) = True.
Proof. exact (TRANS (@lem5105923 A _66537 lt2 _66538 _66539) (@lem5105927 A _66537 lt2 _66538 _66539)). Qed.
Lemma lem5105929 {A : Type'} (_66537 : A) (lt2 : type1402 A) (_66538 : A) (_66539 : A) : True = ((term594 A _66538 lt2 _66537 _66539) = (term600 A _66537 lt2 _66538 _66539)).
Proof. exact (SYM (@lem5105928 A _66537 lt2 _66538 _66539)). Qed.
Lemma lem5105930 {A : Type'} (_66537 : A) (lt2 : type1402 A) (_66538 : A) (_66539 : A) : (term594 A _66538 lt2 _66537 _66539) = (term600 A _66537 lt2 _66538 _66539).
Proof. exact (EQ_MP (@lem5105929 A _66537 lt2 _66538 _66539) (@lem0)). Qed.
Lemma lem5105931 {A : Type'} (_66537 : A) (_66538 : A) (_66539 : A) (lt2 : type1402 A) (h1 : term58 A lt2) : term600 A _66537 lt2 _66538 _66539.
Proof. exact (EQ_MP (@lem5105930 A _66537 lt2 _66538 _66539) (@lem5105791 A _66538 _66537 _66539 lt2 h1)). Qed.
Lemma lem5105933 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5105934 {A : Type'} (_66538 : A) (lt2 : type1402 A) (_66537 : A) (_66539 : A) : (term600 A _66537 lt2 _66538 _66539) = (term604 A _66538 lt2 _66537 _66539).
Proof. exact (@lem5105933 (term554 A _66537 lt2 _66538 _66539) (term549 A lt2 _66537 _66539)). Qed.
Lemma lem5105936 (a : Prop) (b : Prop) : (term605 a b) = (term606 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5105937 {A : Type'} (_66537 : A) (lt2 : type1402 A) (_66538 : A) (_66539 : A) : (term607 A _66537 lt2 _66538 _66539) = (term608 A _66537 lt2 _66538 _66539).
Proof. exact (@lem5105936 (term551 A lt2 _66537 _66538) (term551 A lt2 _66538 _66539)). Qed.
Lemma lem5105939 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5105940 {A : Type'} (lt2 : type1402 A) (_66537 : A) (_66538 : A) : (term609 A lt2 _66537 _66538) = (term549 A lt2 _66537 _66538).
Proof. exact (@lem5105939 (term549 A lt2 _66537 _66538)). Qed.
Lemma lem5105941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5105942 {A : Type'} (lt2 : type1402 A) (_66537 : A) (_66538 : A) : (term610 A lt2 _66537 _66538) = (term611 A lt2 _66537 _66538).
Proof. exact (MK_COMB (@lem5105941) (@lem5105940 A lt2 _66537 _66538)). Qed.
Lemma lem5105944 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5105945 {A : Type'} (lt2 : type1402 A) (_66538 : A) (_66539 : A) : (term609 A lt2 _66538 _66539) = (term549 A lt2 _66538 _66539).
Proof. exact (@lem5105944 (term549 A lt2 _66538 _66539)). Qed.
Lemma lem5105946 {A : Type'} (_66537 : A) (lt2 : type1402 A) (_66538 : A) (_66539 : A) : (term608 A _66537 lt2 _66538 _66539) = (term612 A _66537 lt2 _66538 _66539).
Proof. exact (MK_COMB (@lem5105942 A lt2 _66537 _66538) (@lem5105945 A lt2 _66538 _66539)). Qed.
Lemma lem5105947 {A : Type'} (_66537 : A) (lt2 : type1402 A) (_66538 : A) (_66539 : A) : (term607 A _66537 lt2 _66538 _66539) = (term612 A _66537 lt2 _66538 _66539).
Proof. exact (TRANS (@lem5105937 A _66537 lt2 _66538 _66539) (@lem5105946 A _66537 lt2 _66538 _66539)). Qed.
Lemma lem5105948 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5105949 {A : Type'} (_66537 : A) (lt2 : type1402 A) (_66538 : A) (_66539 : A) : (term613 A _66537 lt2 _66538 _66539) = (term614 A _66537 lt2 _66538 _66539).
Proof. exact (MK_COMB (@lem5105948) (@lem5105947 A _66537 lt2 _66538 _66539)). Qed.
Lemma lem5105950 {A : Type'} (lt2 : type1402 A) (_66537 : A) (_66539 : A) : (term549 A lt2 _66537 _66539) = (term549 A lt2 _66537 _66539).
Proof. exact (eq_refl (term549 A lt2 _66537 _66539)). Qed.
Lemma lem5105951 {A : Type'} (_66538 : A) (lt2 : type1402 A) (_66537 : A) (_66539 : A) : (term604 A _66538 lt2 _66537 _66539) = (term615 A _66538 lt2 _66537 _66539).
Proof. exact (MK_COMB (@lem5105949 A _66537 lt2 _66538 _66539) (@lem5105950 A lt2 _66537 _66539)). Qed.
Lemma lem5105952 {A : Type'} (_66538 : A) (lt2 : type1402 A) (_66537 : A) (_66539 : A) : (term600 A _66537 lt2 _66538 _66539) = (term615 A _66538 lt2 _66537 _66539).
Proof. exact (TRANS (@lem5105934 A _66538 lt2 _66537 _66539) (@lem5105951 A _66538 lt2 _66537 _66539)). Qed.
Lemma lem5105954 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term587 A y lt2 z s n) : term616 A z lt2 y s n.
Proof. exact (conj (@lem5105852 A y lt2 z s n h1) (@lem5105859 A y lt2 z s n h1)). Qed.
Lemma lem5105956 {A : Type'} (_66538 : A) (_66537 : A) (_66539 : A) (lt2 : type1402 A) (h1 : term58 A lt2) : term615 A _66538 lt2 _66537 _66539.
Proof. exact (EQ_MP (@lem5105952 A _66538 lt2 _66537 _66539) (@lem5105931 A _66537 _66538 _66539 lt2 h1)). Qed.
Lemma lem5105957 {A : Type'} (_66538 : A) (_66537 : A) (_66539 : A) (lt2 : type1402 A) (h1 : term58 A lt2) : term615 A _66538 lt2 _66537 _66539.
Proof. exact (@lem5105956 A _66538 _66537 _66539 lt2 h1). Qed.
Lemma lem5105958 {A : Type'} (y : nat) (z : nat) (s : nat -> A) (n : nat) (lt2 : type1402 A) (h1 : term58 A lt2) : term617 A y lt2 z s n.
Proof. exact (@lem5105957 A (@I (nat -> A) s y) (@I (nat -> A) s z) (@I (nat -> A) s n) lt2 h1). Qed.
Lemma lem5105961 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term58 A lt2) (h2 : term587 A y lt2 z s n) : term580 A lt2 z s n.
Proof. exact (@lem5105958 A y z s n lt2 h1 (@lem5105954 A y lt2 z s n h2)). Qed.
Lemma lem5105962 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term58 A lt2) (h2 : term587 A y lt2 z s n) : term595 A lt2 z s n.
Proof. exact (fun h0 : term582 A lt2 z s n => @lem5105961 A y lt2 z s n h1 h2). Qed.
Lemma lem5105964 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5105965 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) : (term595 A lt2 z s n) = (term580 A lt2 z s n).
Proof. exact (@lem5105964 (term580 A lt2 z s n)). Qed.
Lemma lem5105966 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term58 A lt2) (h2 : term587 A y lt2 z s n) : term580 A lt2 z s n.
Proof. exact (EQ_MP (@lem5105965 A lt2 z s n) (@lem5105962 A y lt2 z s n h1 h2)). Qed.
Lemma lem5105969 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5105971 {A : Type'} (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) : (term582 A lt2 z s n) = (term618 A lt2 z s n).
Proof. exact (@lem5105969 (term580 A lt2 z s n)). Qed.
Lemma lem5105974 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term587 A y lt2 z s n) : term618 A lt2 z s n.
Proof. exact (EQ_MP (@lem5105971 A lt2 z s n) (@lem5105809 A y lt2 z s n h1)). Qed.
Lemma lem5105977 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term58 A lt2) (h2 : term587 A y lt2 z s n) : False.
Proof. exact (@lem5105974 A y lt2 z s n h2 (@lem5105966 A y lt2 z s n h1 h2)). Qed.
Lemma lem5105978 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term58 A lt2) (h2 : term587 A y lt2 z s n) : term619.
Proof. exact (fun h0 : ~ False => @lem5105977 A y lt2 z s n h1 h2). Qed.
Lemma lem5105980 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5105981 : term619 = False.
Proof. exact (@lem5105980 False). Qed.
Lemma lem5105982 {A : Type'} (y : nat) (lt2 : type1402 A) (z : nat) (s : nat -> A) (n : nat) (h1 : term58 A lt2) (h2 : term587 A y lt2 z s n) : False.
Proof. exact (EQ_MP (@lem5105981) (@lem5105978 A y lt2 z s n h1 h2)). Qed.
Lemma lem5105984 {A : Type'} (_66554 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term61 A lt2 s) : term571 A lt2 s _66554.
Proof. exact (EQ_MP (@lem5105755 A lt2 s _66554) (@lem5105754 A _66554 lt2 s h1)). Qed.
Lemma lem5105985 {A : Type'} (n : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term61 A lt2 s) : term571 A lt2 s n.
Proof. exact (@lem5105984 A n lt2 s h1). Qed.
Lemma lem5105986 {A : Type'} (n : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term61 A lt2 s) : term620 A lt2 s n.
Proof. exact (fun h0 : term574 A lt2 s n => @lem5105985 A n lt2 s h1). Qed.
Lemma lem5105988 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5105989 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term620 A lt2 s n) = (term571 A lt2 s n).
Proof. exact (@lem5105988 (term571 A lt2 s n)). Qed.
Lemma lem5105990 {A : Type'} (n : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term61 A lt2 s) : term571 A lt2 s n.
Proof. exact (EQ_MP (@lem5105989 A lt2 s n) (@lem5105986 A n lt2 s h1)). Qed.
Lemma lem5105993 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5105995 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term574 A lt2 s n) = (term621 A lt2 s n).
Proof. exact (@lem5105993 (term571 A lt2 s n)). Qed.
Lemma lem5105998 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term574 A lt2 s n) : term621 A lt2 s n.
Proof. exact (EQ_MP (@lem5105995 A lt2 s n) (@lem5105845 A lt2 s n h1)). Qed.
Lemma lem5106001 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term61 A lt2 s) (h2 : term574 A lt2 s n) : False.
Proof. exact (@lem5105998 A lt2 s n h2 (@lem5105990 A n lt2 s h1)). Qed.
Lemma lem5106002 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term61 A lt2 s) (h2 : term574 A lt2 s n) : term619.
Proof. exact (fun h0 : ~ False => @lem5106001 A lt2 s n h1 h2). Qed.
Lemma lem5106004 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5106005 : term619 = False.
Proof. exact (@lem5106004 False). Qed.
Lemma lem5106006 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term61 A lt2 s) (h2 : term574 A lt2 s n) : False.
Proof. exact (EQ_MP (@lem5106005) (@lem5106002 A lt2 s n h1 h2)). Qed.
Lemma lem5106007 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term61 A lt2 s) (h2 : term574 A lt2 s n) : (term574 A lt2 s n) = False.
Proof. exact (prop_ext (fun h3 : term574 A lt2 s n => @lem5106006 A lt2 s n h1 h2) (fun h3 : False => @lem5105845 A lt2 s n h2)). Qed.
Lemma lem5106008 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term61 A lt2 s) (h2 : term574 A lt2 s n) : False.
Proof. exact (EQ_MP (@lem5106007 A lt2 s n h1 h2) (@lem5105845 A lt2 s n h2)). Qed.
Lemma lem5106009 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term61 A lt2 s) (h2 : term574 A lt2 s n) : (term574 A lt2 s n) = False.
Proof. exact (prop_ext (fun h3 : term574 A lt2 s n => @lem5106008 A lt2 s n h1 h2) (fun h3 : False => @lem5105699 A lt2 s n h2)). Qed.
Lemma lem5106010 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term61 A lt2 s) (h2 : term574 A lt2 s n) : False.
Proof. exact (EQ_MP (@lem5106009 A lt2 s n h1 h2) (@lem5105699 A lt2 s n h2)). Qed.
Lemma lem5106011 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term61 A lt2 s) (h2 : term574 A lt2 s n) : (term574 A lt2 s n) = False.
Proof. exact (prop_ext (fun h3 : term574 A lt2 s n => @lem5106010 A lt2 s n h1 h2) (fun h3 : False => @lem5105699 A lt2 s n h2)). Qed.
Lemma lem5106012 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term61 A lt2 s) (h2 : term574 A lt2 s n) : False.
Proof. exact (EQ_MP (@lem5106011 A lt2 s n h1 h2) (@lem5105699 A lt2 s n h2)). Qed.
Lemma lem5106013 {A : Type'} (y : nat) (z : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term58 A lt2) (h2 : term61 A lt2 s) (h3 : term541 A y z lt2 s n) : False.
Proof. exact (or_elim (@lem5105224 A y z lt2 s n h3) (fun h0 : term587 A y lt2 z s n => @lem5105982 A y lt2 z s n h1 h0) (fun h0 : term574 A lt2 s n => @lem5106012 A lt2 s n h2 h0)). Qed.
Lemma lem5106014 {A : Type'} (_66533 : type418 A) (y : nat) (z : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term58 A lt2) (h2 : term228 A _66533) (h3 : term61 A lt2 s) (h4 : term541 A y z lt2 s n) : False.
Proof. exact (ex_elim (@lem5104564 A _66533 h2) (fun y' : type417 A => fun h0 : term434 A _66533 y' => @lem5106013 A y z lt2 s n h1 h3 h4)). Qed.
Lemma lem5106015 {A : Type'} (_66533 : type418 A) (y : nat) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term58 A lt2) (h2 : term228 A _66533) (h3 : term61 A lt2 s) (h4 : term544 A y lt2 s n) : False.
Proof. exact (ex_elim (@lem5104906 A y lt2 s n h4) (fun z : nat => fun h0 : term543 A y lt2 s n z => @lem5106014 A _66533 y z lt2 s n h1 h2 h3 h0)). Qed.
Lemma lem5106016 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (s : nat -> A) (n : nat) (h1 : term58 A lt2) (h2 : term228 A _66533) (h3 : term61 A lt2 s) (h4 : term546 A lt2 s n) : False.
Proof. exact (ex_elim (@lem5104905 A lt2 s n h4) (fun y : nat => fun h0 : term545 A lt2 s n y => @lem5106015 A _66533 y lt2 s n h1 h2 h3 h0)). Qed.
Lemma lem5106017 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term228 A _66533) (h3 : term61 A lt2 s) (h4 : term115 A lt2 s) : False.
Proof. exact (ex_elim (@lem5104904 A lt2 s h4) (fun n : nat => fun h0 : term547 A lt2 s n => @lem5106016 A _66533 lt2 s n h1 h2 h3 h0)). Qed.
Lemma lem5106018 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term228 A _66533) (h3 : term61 A lt2 s) (h4 : term115 A lt2 s) : (term61 A lt2 s) = False.
Proof. exact (prop_ext (fun h5 : term61 A lt2 s => @lem5106017 A _66533 lt2 s h1 h2 h3 h4) (fun h5 : False => @lem5104686 A lt2 s h3)). Qed.
Lemma lem5106019 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term228 A _66533) (h3 : term61 A lt2 s) (h4 : term115 A lt2 s) : False.
Proof. exact (EQ_MP (@lem5106018 A _66533 lt2 s h1 h2 h3 h4) (@lem5104686 A lt2 s h3)). Qed.
Lemma lem5106020 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term228 A _66533) (h3 : term61 A lt2 s) (h4 : term115 A lt2 s) : (term115 A lt2 s) = False.
Proof. exact (prop_ext (fun h5 : term115 A lt2 s => @lem5106019 A _66533 lt2 s h1 h2 h3 h4) (fun h5 : False => @lem5103946 A lt2 s h4)). Qed.
Lemma lem5106021 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term228 A _66533) (h3 : term61 A lt2 s) (h4 : term115 A lt2 s) : False.
Proof. exact (EQ_MP (@lem5106020 A _66533 lt2 s h1 h2 h3 h4) (@lem5103946 A lt2 s h4)). Qed.
Lemma lem5106022 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term228 A _66533) (h3 : term61 A lt2 s) : term114 A lt2 s.
Proof. exact (fun h0 : term115 A lt2 s => @lem5106021 A _66533 lt2 s h1 h2 h3 h0). Qed.
Lemma lem5106023 {A : Type'} (_66533 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term228 A _66533) (h3 : term61 A lt2 s) : term99 A lt2 s.
Proof. exact (EQ_MP (@lem5103945 A lt2 s) (@lem5106022 A _66533 lt2 s h1 h2 h3)). Qed.
Lemma lem5106024 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (_66533 : type418 A) (h1 : term58 A lt2) (h2 : term228 A _66533) : term124 A lt2 s.
Proof. exact (fun h0 : term61 A lt2 s => @lem5106023 A _66533 lt2 s h1 h2 h0). Qed.
Lemma lem5106025 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (_66533 : type418 A) (h1 : term58 A lt2) (h2 : term228 A _66533) : term156 A _66533 lt2 s.
Proof. exact (fun h0 : term154 A _66533 lt2 => @lem5106024 A s lt2 _66533 h1 h2). Qed.
Lemma lem5106026 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66533 : type418 A) (h1 : term228 A _66533) : term163 A _66533 lt2 s.
Proof. exact (fun h0 : term58 A lt2 => @lem5106025 A s lt2 _66533 h0 h1). Qed.
Lemma lem5106027 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66533 : type418 A) (h1 : term228 A _66533) : term166 A _66533 lt2 s.
Proof. exact (fun h0 : term56 A lt2 => @lem5106026 A lt2 s _66533 h1). Qed.
Lemma lem5106032 {A : Type'} (s : nat -> A) (_66533 : type418 A) (h1 : term228 A _66533) : term168 A _66533 s.
Proof. exact (fun lt2 : type1402 A => @lem5106027 A lt2 s _66533 h1). Qed.
Lemma lem5106037 {A : Type'} (_66533 : type418 A) (h1 : term228 A _66533) : term170 A _66533.
Proof. exact (fun s : nat -> A => @lem5106032 A s _66533 h1). Qed.
Lemma lem5106038 {A : Type'} (_66533 : type418 A) : term230 A _66533.
Proof. exact (fun h0 : term228 A _66533 => @lem5106037 A _66533 h0). Qed.
Lemma lem5106043 {A : Type'} : term232 A.
Proof. exact (fun _66533 : type418 A => @lem5106038 A _66533). Qed.
Lemma lem5106044 {A : Type'} : term139 A.
Proof. exact (EQ_MP (@lem5103936 A) (@lem5106043 A)). Qed.
Lemma lem5106045 {A : Type'} (s : nat -> A) : term622 A s.
Proof. exact (@lem5106044 A s). Qed.
Lemma lem5106046 {A : Type'} (s : nat -> A) : (term622 A s) = (term135 A s).
Proof. exact (eq_refl (term622 A s)). Qed.
Lemma lem5106047 {A : Type'} (s : nat -> A) : term135 A s.
Proof. exact (EQ_MP (@lem5106046 A s) (@lem5106045 A s)). Qed.
Lemma lem5106048 {A : Type'} (s : nat -> A) (lt2 : type1402 A) : term623 A s lt2.
Proof. exact (@lem5106047 A s lt2). Qed.
Lemma lem5106049 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term623 A s lt2) = (term116 A lt2 s).
Proof. exact (eq_refl (term623 A s lt2)). Qed.
Lemma lem5106050 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term116 A lt2 s.
Proof. exact (EQ_MP (@lem5106049 A lt2 s) (@lem5106048 A s lt2)). Qed.
Lemma lem5106052 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term116 A lt2 s.
Proof. exact (@lem5103341 A lt2 s (@lem5106050 A lt2 s)). Qed.
Lemma lem5106053 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (h1 : term56 A lt2) : term129 A lt2 s.
Proof. exact (@lem5106052 A lt2 s (@lem5103242 A lt2 h1)). Qed.
Lemma lem5106054 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (h1 : term58 A lt2) (h2 : term56 A lt2) : term126 A lt2 s.
Proof. exact (@lem5106053 A s lt2 h2 (@lem5103244 A lt2 h1)). Qed.
Lemma lem5106055 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) : term123 A lt2 s.
Proof. exact (@lem5106054 A s lt2 h1 h3 (@lem5103243 A lt2 h2)). Qed.
Lemma lem5106056 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term61 A lt2 s) : term114 A lt2 s.
Proof. exact (@lem5106055 A s lt2 h1 h2 h3 (@lem5103258 A lt2 s h4)). Qed.
Lemma lem5106057 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term61 A lt2 s) (h5 : term115 A lt2 s) : False.
Proof. exact (@lem5106056 A lt2 s h1 h2 h3 h4 (@lem5103325 A lt2 s h5)). Qed.
Lemma lem5106058 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term61 A lt2 s) (h5 : term115 A lt2 s) : (term115 A lt2 s) = False.
Proof. exact (prop_ext (fun h6 : term115 A lt2 s => @lem5106057 A lt2 s h1 h2 h3 h4 h5) (fun h6 : False => @lem5103325 A lt2 s h5)). Qed.
Lemma lem5106059 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term61 A lt2 s) (h5 : term115 A lt2 s) : False.
Proof. exact (EQ_MP (@lem5106058 A lt2 s h1 h2 h3 h4 h5) (@lem5103325 A lt2 s h5)). Qed.
Lemma lem5106060 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term61 A lt2 s) : term114 A lt2 s.
Proof. exact (fun h0 : term115 A lt2 s => @lem5106059 A lt2 s h1 h2 h3 h4 h0). Qed.
Lemma lem5106061 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term61 A lt2 s) : term99 A lt2 s.
Proof. exact (EQ_MP (@lem5103324 A lt2 s) (@lem5106060 A lt2 s h1 h2 h3 h4)). Qed.
Lemma lem5106062 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term61 A lt2 s) : term62 A lt2 s.
Proof. exact (@lem5103320 A lt2 s (@lem5106061 A lt2 s h1 h2 h3 h4)). Qed.
Lemma lem5106064 (p : Prop) (q : Prop) (r : Prop) : term624 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem5106065 {A : Type'} (s : nat -> A) : term625 A s.
Proof. exact (@lem5106064 (term626 A s) (term627 A s) False). Qed.
Lemma lem5106067 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5106068 {A : Type'} (s : nat -> A) : (term626 A s) = (term628 A s).
Proof. exact (@lem5106067 (term626 A s)). Qed.
Lemma lem5106069 {A : Type'} (s : nat -> A) : (term628 A s) = (term626 A s).
Proof. exact (SYM (@lem5106068 A s)). Qed.
Lemma lem5106070 {A : Type'} (s : nat -> A) (h1 : term629 A s) : term629 A s.
Proof. exact (h1). Qed.
Lemma lem5106073 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term630 A lt2 s) : term630 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem5106074 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term631 A lt2 s.
Proof. exact (fun h0 : term630 A lt2 s => @lem5106073 A lt2 s h0). Qed.
Lemma lem5106075 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term631 A lt2 s) : term631 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem5106076 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term630 A lt2 s) : term630 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem5106077 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term630 A lt2 s) (h2 : term631 A lt2 s) : term630 A lt2 s.
Proof. exact (@lem5106075 A lt2 s h2 (@lem5106076 A lt2 s h1)). Qed.
Lemma lem5106078 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term630 A lt2 s) : term632 A lt2 s.
Proof. exact (fun h0 : term631 A lt2 s => @lem5106077 A lt2 s h1 h0). Qed.
Lemma lem5106079 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term631 A lt2 s) : term631 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem5106080 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term630 A lt2 s) (h2 : term631 A lt2 s) : term630 A lt2 s.
Proof. exact (@lem5106078 A lt2 s h1 (@lem5106079 A lt2 s h2)). Qed.
Lemma lem5106081 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term631 A lt2 s) : term631 A lt2 s.
Proof. exact (fun h0 : term630 A lt2 s => @lem5106080 A lt2 s h0 h1). Qed.
Lemma lem5106082 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term633 A lt2 s.
Proof. exact (fun h0 : term631 A lt2 s => @lem5106081 A lt2 s h0). Qed.
Lemma lem5106085 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term631 A lt2 s.
Proof. exact (@lem5106082 A lt2 s (@lem5106074 A lt2 s)). Qed.
Lemma lem5106086 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term631 A lt2 s.
Proof. exact (@lem5106085 A lt2 s). Qed.
Lemma lem5106160 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5106161 : term634 = term635.
Proof. exact (@lem5106160 term636). Qed.
Lemma lem5106218 {A : Type'} (s : nat -> A) : (term637 A s) = (term637 A s).
Proof. exact (eq_refl (term637 A s)). Qed.
Lemma lem5106219 {A : Type'} (s : nat -> A) : (term638 A s) = (term639 A s).
Proof. exact (MK_COMB (@lem5106218 A s) (@lem5106161)). Qed.
Lemma lem5106222 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term640 A lt2 s) = (term640 A lt2 s).
Proof. exact (eq_refl (term640 A lt2 s)). Qed.
Lemma lem5106223 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term641 A lt2 s) = (term642 A lt2 s).
Proof. exact (MK_COMB (@lem5106222 A lt2 s) (@lem5106219 A s)). Qed.
Lemma lem5106226 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term122 A lt2 s) = (term122 A lt2 s).
Proof. exact (eq_refl (term122 A lt2 s)). Qed.
Lemma lem5106227 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term643 A lt2 s) = (term644 A lt2 s).
Proof. exact (MK_COMB (@lem5106226 A lt2 s) (@lem5106223 A lt2 s)). Qed.
Lemma lem5106230 {A : Type'} (lt2 : type1402 A) : (term125 A lt2) = (term125 A lt2).
Proof. exact (eq_refl (term125 A lt2)). Qed.
Lemma lem5106231 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term645 A lt2 s) = (term646 A lt2 s).
Proof. exact (MK_COMB (@lem5106230 A lt2) (@lem5106227 A lt2 s)). Qed.
Lemma lem5106234 {A : Type'} (lt2 : type1402 A) : (term128 A lt2) = (term128 A lt2).
Proof. exact (eq_refl (term128 A lt2)). Qed.
Lemma lem5106235 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term647 A lt2 s) = (term648 A lt2 s).
Proof. exact (MK_COMB (@lem5106234 A lt2) (@lem5106231 A lt2 s)). Qed.
Lemma lem5106238 {A : Type'} (lt2 : type1402 A) : (term131 A lt2) = (term131 A lt2).
Proof. exact (eq_refl (term131 A lt2)). Qed.
Lemma lem5106239 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term630 A lt2 s) = (term649 A lt2 s).
Proof. exact (MK_COMB (@lem5106238 A lt2) (@lem5106235 A lt2 s)). Qed.
Lemma lem5106242 {A : Type'} (s : nat -> A) : (term650 A s) = (term651 A s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5106239 A lt2 s)). Qed.
Lemma lem5106243 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5106244 {A : Type'} (s : nat -> A) : (term652 A s) = (term653 A s).
Proof. exact (MK_COMB (@lem5106243 A) (@lem5106242 A s)). Qed.
Lemma lem5106249 {A : Type'} : (term654 A) = (term655 A).
Proof. exact (fun_ext (fun s : nat -> A => @lem5106244 A s)). Qed.
Lemma lem5106250 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5106257 {A : Type'} : (term656 A) = (term657 A).
Proof. exact (MK_COMB (@lem5106250 A) (@lem5106249 A)). Qed.
Lemma lem5106258 {A : Type'} (_66562 : type418 A) (h1 : _66562 = (term141 A)) : _66562 = (term141 A).
Proof. exact (h1). Qed.
Lemma lem5106259 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem5106260 {A : Type'} (lt2 : type1402 A) (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (_66562 lt2) = (term142 A lt2).
Proof. exact (MK_COMB (@lem5106258 A _66562 h1) (@lem5106259 A lt2)). Qed.
Lemma lem5106261 {A : Type'} (lt2 : type1402 A) : (term142 A lt2) = (term143 A lt2).
Proof. exact (eq_refl (term142 A lt2)). Qed.
Lemma lem5106262 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term144 A _66562 lt2) = (term144 A _66562 lt2).
Proof. exact (eq_refl (term144 A _66562 lt2)). Qed.
Lemma lem5106263 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : ((_66562 lt2) = (term142 A lt2)) = ((_66562 lt2) = (term143 A lt2)).
Proof. exact (MK_COMB (@lem5106262 A _66562 lt2) (@lem5106261 A lt2)). Qed.
Lemma lem5106264 {A : Type'} (lt2 : type1402 A) (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (_66562 lt2) = (term143 A lt2).
Proof. exact (EQ_MP (@lem5106263 A _66562 lt2) (@lem5106260 A lt2 _66562 h1)). Qed.
Lemma lem5106265 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5106266 {A : Type'} (lt2 : type1402 A) (x : A) (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (_66562 lt2 x) = (term145 A lt2 x).
Proof. exact (MK_COMB (@lem5106264 A lt2 _66562 h1) (@lem5106265 A x)). Qed.
Lemma lem5106267 {A : Type'} (lt2 : type1402 A) (x : A) : (term145 A lt2 x) = (term146 A lt2 x).
Proof. exact (eq_refl (term145 A lt2 x)). Qed.
Lemma lem5106268 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term147 A _66562 lt2 x) = (term147 A _66562 lt2 x).
Proof. exact (eq_refl (term147 A _66562 lt2 x)). Qed.
Lemma lem5106269 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : ((_66562 lt2 x) = (term145 A lt2 x)) = ((_66562 lt2 x) = (term146 A lt2 x)).
Proof. exact (MK_COMB (@lem5106268 A _66562 lt2 x) (@lem5106267 A lt2 x)). Qed.
Lemma lem5106270 {A : Type'} (lt2 : type1402 A) (x : A) (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (_66562 lt2 x) = (term146 A lt2 x).
Proof. exact (EQ_MP (@lem5106269 A _66562 lt2 x) (@lem5106266 A lt2 x _66562 h1)). Qed.
Lemma lem5106292 (m : nat) (n : nat) : (term658 m n) = (term658 m n).
Proof. exact (eq_refl (term658 m n)). Qed.
Lemma lem5106293 (m : nat) : (term659 m) = (term659 m).
Proof. exact (fun_ext (fun n : nat => @lem5106292 m n)). Qed.
Lemma lem5106294 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5106295 (m : nat) : (term660 m) = (term660 m).
Proof. exact (MK_COMB (@lem5106294) (@lem5106293 m)). Qed.
Lemma lem5106296 : term661 = term661.
Proof. exact (fun_ext (fun m : nat => @lem5106295 m)). Qed.
Lemma lem5106297 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5106298 : term636 = term636.
Proof. exact (MK_COMB (@lem5106297) (@lem5106296)). Qed.
Lemma lem5106299 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5106300 : term635 = term635.
Proof. exact (MK_COMB (@lem5106299) (@lem5106298)). Qed.
Lemma lem5106317 {A : Type'} (s : nat -> A) (x : nat) (y : nat) : (term662 A s x y) = (term662 A s x y).
Proof. exact (eq_refl (term662 A s x y)). Qed.
Lemma lem5106318 {A : Type'} (s : nat -> A) (x : nat) : (term663 A s x) = (term663 A s x).
Proof. exact (fun_ext (fun y : nat => @lem5106317 A s x y)). Qed.
Lemma lem5106319 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5106320 {A : Type'} (s : nat -> A) (x : nat) : (term664 A s x) = (term664 A s x).
Proof. exact (MK_COMB (@lem5106319) (@lem5106318 A s x)). Qed.
Lemma lem5106321 {A : Type'} (s : nat -> A) : (term665 A s) = (term665 A s).
Proof. exact (fun_ext (fun x : nat => @lem5106320 A s x)). Qed.
Lemma lem5106322 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5106323 {A : Type'} (s : nat -> A) : (term626 A s) = (term626 A s).
Proof. exact (MK_COMB (@lem5106322) (@lem5106321 A s)). Qed.
Lemma lem5106324 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5106325 {A : Type'} (s : nat -> A) : (term629 A s) = (term629 A s).
Proof. exact (MK_COMB (@lem5106324) (@lem5106323 A s)). Qed.
Lemma lem5106326 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5106327 {A : Type'} (s : nat -> A) : (term637 A s) = (term637 A s).
Proof. exact (MK_COMB (@lem5106326) (@lem5106325 A s)). Qed.
Lemma lem5106328 {A : Type'} (s : nat -> A) : (term639 A s) = (term639 A s).
Proof. exact (MK_COMB (@lem5106327 A s) (@lem5106300)). Qed.
Lemma lem5106345 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term104 A lt2 n s m) = (term104 A lt2 n s m).
Proof. exact (eq_refl (term104 A lt2 n s m)). Qed.
Lemma lem5106346 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term106 A lt2 s m) = (term106 A lt2 s m).
Proof. exact (fun_ext (fun n : nat => @lem5106345 A lt2 n s m)). Qed.
Lemma lem5106347 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5106348 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term108 A lt2 s m) = (term108 A lt2 s m).
Proof. exact (MK_COMB (@lem5106347) (@lem5106346 A lt2 s m)). Qed.
Lemma lem5106349 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term110 A lt2 s) = (term110 A lt2 s).
Proof. exact (fun_ext (fun m : nat => @lem5106348 A lt2 s m)). Qed.
Lemma lem5106350 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5106351 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term62 A lt2 s) = (term62 A lt2 s).
Proof. exact (MK_COMB (@lem5106350) (@lem5106349 A lt2 s)). Qed.
Lemma lem5106352 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5106353 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term640 A lt2 s) = (term640 A lt2 s).
Proof. exact (MK_COMB (@lem5106352) (@lem5106351 A lt2 s)). Qed.
Lemma lem5106354 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term642 A lt2 s) = (term642 A lt2 s).
Proof. exact (MK_COMB (@lem5106353 A lt2 s) (@lem5106328 A s)). Qed.
Lemma lem5106365 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term94 A lt2 s n) = (term94 A lt2 s n).
Proof. exact (eq_refl (term94 A lt2 s n)). Qed.
Lemma lem5106366 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term96 A lt2 s) = (term96 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5106365 A lt2 s n)). Qed.
Lemma lem5106367 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5106368 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term61 A lt2 s) = (term61 A lt2 s).
Proof. exact (MK_COMB (@lem5106367) (@lem5106366 A lt2 s)). Qed.
Lemma lem5106369 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5106370 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term122 A lt2 s) = (term122 A lt2 s).
Proof. exact (MK_COMB (@lem5106369) (@lem5106368 A lt2 s)). Qed.
Lemma lem5106371 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term644 A lt2 s) = (term644 A lt2 s).
Proof. exact (MK_COMB (@lem5106370 A lt2 s) (@lem5106354 A lt2 s)). Qed.
Lemma lem5106373 {A : Type'} (lt2 : type1402 A) (x : A) (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (term146 A lt2 x) = (_66562 lt2 x).
Proof. exact (SYM (@lem5106270 A lt2 x _66562 h1)). Qed.
Lemma lem5106374 {A : Type'} (lt2 : type1402 A) (x : A) (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (term146 A lt2 x) = (_66562 lt2 x).
Proof. exact (@lem5106373 A lt2 x _66562 h1). Qed.
Lemma lem5106375 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5106376 {A : Type'} (lt2 : type1402 A) (x : A) (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (term148 A lt2 x) = (term149 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5106375 A) (@lem5106374 A lt2 x _66562 h1)). Qed.
Lemma lem5106377 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem5106378 {A : Type'} (lt2 : type1402 A) (x : A) (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (term150 A lt2 x) = (term151 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5106377 A) (@lem5106376 A lt2 x _66562 h1)). Qed.
Lemma lem5106379 {A : Type'} (lt2 : type1402 A) (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (term152 A lt2) = (term153 A _66562 lt2).
Proof. exact (fun_ext (fun x : A => @lem5106378 A lt2 x _66562 h1)). Qed.
Lemma lem5106380 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106381 {A : Type'} (lt2 : type1402 A) (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (term57 A lt2) = (term154 A _66562 lt2).
Proof. exact (MK_COMB (@lem5106380 A) (@lem5106379 A lt2 _66562 h1)). Qed.
Lemma lem5106382 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5106383 {A : Type'} (lt2 : type1402 A) (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (term125 A lt2) = (term155 A _66562 lt2).
Proof. exact (MK_COMB (@lem5106382) (@lem5106381 A lt2 _66562 h1)). Qed.
Lemma lem5106384 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (term646 A lt2 s) = (term666 A _66562 lt2 s).
Proof. exact (MK_COMB (@lem5106383 A lt2 _66562 h1) (@lem5106371 A lt2 s)). Qed.
Lemma lem5106405 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term157 A y lt2 x z) = (term157 A y lt2 x z).
Proof. exact (eq_refl (term157 A y lt2 x z)). Qed.
Lemma lem5106406 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term158 A y lt2 x) = (term158 A y lt2 x).
Proof. exact (fun_ext (fun z : A => @lem5106405 A y lt2 x z)). Qed.
Lemma lem5106407 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106408 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term159 A y lt2 x) = (term159 A y lt2 x).
Proof. exact (MK_COMB (@lem5106407 A) (@lem5106406 A y lt2 x)). Qed.
Lemma lem5106409 {A : Type'} (lt2 : type1402 A) (x : A) : (term160 A lt2 x) = (term160 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5106408 A y lt2 x)). Qed.
Lemma lem5106410 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106411 {A : Type'} (lt2 : type1402 A) (x : A) : (term161 A lt2 x) = (term161 A lt2 x).
Proof. exact (MK_COMB (@lem5106410 A) (@lem5106409 A lt2 x)). Qed.
Lemma lem5106412 {A : Type'} (lt2 : type1402 A) : (term162 A lt2) = (term162 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5106411 A lt2 x)). Qed.
Lemma lem5106413 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106414 {A : Type'} (lt2 : type1402 A) : (term58 A lt2) = (term58 A lt2).
Proof. exact (MK_COMB (@lem5106413 A) (@lem5106412 A lt2)). Qed.
Lemma lem5106415 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5106416 {A : Type'} (lt2 : type1402 A) : (term128 A lt2) = (term128 A lt2).
Proof. exact (MK_COMB (@lem5106415) (@lem5106414 A lt2)). Qed.
Lemma lem5106417 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (term648 A lt2 s) = (term667 A _66562 lt2 s).
Proof. exact (MK_COMB (@lem5106416 A lt2) (@lem5106384 A lt2 s _66562 h1)). Qed.
Lemma lem5106424 {A : Type'} (lt2 : type1402 A) (x : A) : (term164 A lt2 x) = (term164 A lt2 x).
Proof. exact (eq_refl (term164 A lt2 x)). Qed.
Lemma lem5106425 {A : Type'} (lt2 : type1402 A) : (term165 A lt2) = (term165 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5106424 A lt2 x)). Qed.
Lemma lem5106426 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106427 {A : Type'} (lt2 : type1402 A) : (term56 A lt2) = (term56 A lt2).
Proof. exact (MK_COMB (@lem5106426 A) (@lem5106425 A lt2)). Qed.
Lemma lem5106428 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5106429 {A : Type'} (lt2 : type1402 A) : (term131 A lt2) = (term131 A lt2).
Proof. exact (MK_COMB (@lem5106428) (@lem5106427 A lt2)). Qed.
Lemma lem5106430 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (term649 A lt2 s) = (term668 A _66562 lt2 s).
Proof. exact (MK_COMB (@lem5106429 A lt2) (@lem5106417 A lt2 s _66562 h1)). Qed.
Lemma lem5106431 {A : Type'} (s : nat -> A) (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (term651 A s) = (term669 A _66562 s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5106430 A lt2 s _66562 h1)). Qed.
Lemma lem5106432 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5106433 {A : Type'} (s : nat -> A) (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (term653 A s) = (term670 A _66562 s).
Proof. exact (MK_COMB (@lem5106432 A) (@lem5106431 A s _66562 h1)). Qed.
Lemma lem5106434 {A : Type'} (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (term655 A) = (term671 A _66562).
Proof. exact (fun_ext (fun s : nat -> A => @lem5106433 A s _66562 h1)). Qed.
Lemma lem5106435 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5106436 {A : Type'} (_66562 : type418 A) (h1 : _66562 = (term141 A)) : (term657 A) = (term672 A _66562).
Proof. exact (MK_COMB (@lem5106435 A) (@lem5106434 A _66562 h1)). Qed.
Lemma lem5106437 {A : Type'} (_66562 : type418 A) : term673 A _66562.
Proof. exact (fun h0 : _66562 = (term141 A) => @lem5106436 A _66562 h0). Qed.
Lemma lem5106438 {A : Type'} : term674 A.
Proof. exact (fun _66562 : type418 A => @lem5106437 A _66562). Qed.
Lemma lem5106440 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term173 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem5106441 {A : Type'} (P : Prop) (c : type418 A) (Q : type84 A) : term174 A P c Q.
Proof. exact (@lem5106440 (type418 A) P c Q). Qed.
Lemma lem5106442 {A : Type'} : term675 A.
Proof. exact (@lem5106441 A (term657 A) (term141 A) (term676 A)). Qed.
Lemma lem5106443 {A : Type'} (_66562 : type418 A) : (term677 A _66562) = (term672 A _66562).
Proof. exact (eq_refl (term677 A _66562)). Qed.
Lemma lem5106444 {A : Type'} : (term678 A) = (term678 A).
Proof. exact (eq_refl (term678 A)). Qed.
Lemma lem5106445 {A : Type'} (_66562 : type418 A) : ((term657 A) = (term677 A _66562)) = ((term657 A) = (term672 A _66562)).
Proof. exact (MK_COMB (@lem5106444 A) (@lem5106443 A _66562)). Qed.
Lemma lem5106446 {A : Type'} (_66562 : type418 A) : (term179 A _66562) = (term179 A _66562).
Proof. exact (eq_refl (term179 A _66562)). Qed.
Lemma lem5106447 {A : Type'} (_66562 : type418 A) : (term679 A _66562) = (term673 A _66562).
Proof. exact (MK_COMB (@lem5106446 A _66562) (@lem5106445 A _66562)). Qed.
Lemma lem5106448 {A : Type'} : (term680 A) = (term681 A).
Proof. exact (fun_ext (fun _66562 : type418 A => @lem5106447 A _66562)). Qed.
Lemma lem5106449 {A : Type'} : (@all ((A -> A -> Prop) -> A -> A -> Prop)) = (@all ((A -> A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem5106450 {A : Type'} : (term682 A) = (term674 A).
Proof. exact (MK_COMB (@lem5106449 A) (@lem5106448 A)). Qed.
Lemma lem5106451 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5106452 {A : Type'} : (term683 A) = (term684 A).
Proof. exact (MK_COMB (@lem5106451) (@lem5106450 A)). Qed.
Lemma lem5106453 {A : Type'} (_66562 : type418 A) : (term677 A _66562) = (term672 A _66562).
Proof. exact (eq_refl (term677 A _66562)). Qed.
Lemma lem5106454 {A : Type'} (_66562 : type418 A) : (term179 A _66562) = (term179 A _66562).
Proof. exact (eq_refl (term179 A _66562)). Qed.
Lemma lem5106455 {A : Type'} (_66562 : type418 A) : (term685 A _66562) = (term686 A _66562).
Proof. exact (MK_COMB (@lem5106454 A _66562) (@lem5106453 A _66562)). Qed.
Lemma lem5106456 {A : Type'} : (term687 A) = (term688 A).
Proof. exact (fun_ext (fun _66562 : type418 A => @lem5106455 A _66562)). Qed.
Lemma lem5106457 {A : Type'} : (@all ((A -> A -> Prop) -> A -> A -> Prop)) = (@all ((A -> A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem5106458 {A : Type'} : (term689 A) = (term690 A).
Proof. exact (MK_COMB (@lem5106457 A) (@lem5106456 A)). Qed.
Lemma lem5106459 {A : Type'} : (term678 A) = (term678 A).
Proof. exact (eq_refl (term678 A)). Qed.
Lemma lem5106460 {A : Type'} : ((term657 A) = (term689 A)) = ((term657 A) = (term690 A)).
Proof. exact (MK_COMB (@lem5106459 A) (@lem5106458 A)). Qed.
Lemma lem5106461 {A : Type'} : (term675 A) = (term691 A).
Proof. exact (MK_COMB (@lem5106452 A) (@lem5106460 A)). Qed.
Lemma lem5106462 {A : Type'} : term691 A.
Proof. exact (EQ_MP (@lem5106461 A) (@lem5106442 A)). Qed.
Lemma lem5106463 {A : Type'} : (term657 A) = (term690 A).
Proof. exact (@lem5106462 A (@lem5106438 A)). Qed.
Lemma lem5106465 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term193 _3571 _3575 t)) = (term194 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5106466 {A : Type'} (s : type418 A) (t : type418 A) : (s = (term195 A t)) = (term196 A s t).
Proof. exact (@lem5106465 (type1402 A) (type1402 A) s t). Qed.
Lemma lem5106467 {A : Type'} (_66562 : type418 A) : (_66562 = (term197 A)) = (term198 A _66562).
Proof. exact (@lem5106466 A _66562 (term141 A)). Qed.
Lemma lem5106468 {A : Type'} (lt2 : type1402 A) : (term142 A lt2) = (term143 A lt2).
Proof. exact (eq_refl (term142 A lt2)). Qed.
Lemma lem5106469 {A : Type'} : (term197 A) = (term141 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5106468 A lt2)). Qed.
Lemma lem5106470 {A : Type'} (_66562 : type418 A) : (@eq ((A -> A -> Prop) -> A -> A -> Prop) _66562) = (@eq ((A -> A -> Prop) -> A -> A -> Prop) _66562).
Proof. exact (eq_refl (@eq ((A -> A -> Prop) -> A -> A -> Prop) _66562)). Qed.
Lemma lem5106471 {A : Type'} (_66562 : type418 A) : (_66562 = (term197 A)) = (_66562 = (term141 A)).
Proof. exact (MK_COMB (@lem5106470 A _66562) (@lem5106469 A)). Qed.
Lemma lem5106472 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5106473 {A : Type'} (_66562 : type418 A) : (term199 A _66562) = (term200 A _66562).
Proof. exact (MK_COMB (@lem5106472) (@lem5106471 A _66562)). Qed.
Lemma lem5106474 {A : Type'} (lt2 : type1402 A) : (term142 A lt2) = (term143 A lt2).
Proof. exact (eq_refl (term142 A lt2)). Qed.
Lemma lem5106475 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term144 A _66562 lt2) = (term144 A _66562 lt2).
Proof. exact (eq_refl (term144 A _66562 lt2)). Qed.
Lemma lem5106476 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : ((_66562 lt2) = (term142 A lt2)) = ((_66562 lt2) = (term143 A lt2)).
Proof. exact (MK_COMB (@lem5106475 A _66562 lt2) (@lem5106474 A lt2)). Qed.
Lemma lem5106477 {A : Type'} (_66562 : type418 A) : (term201 A _66562) = (term202 A _66562).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5106476 A _66562 lt2)). Qed.
Lemma lem5106478 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5106479 {A : Type'} (_66562 : type418 A) : (term198 A _66562) = (term203 A _66562).
Proof. exact (MK_COMB (@lem5106478 A) (@lem5106477 A _66562)). Qed.
Lemma lem5106480 {A : Type'} (_66562 : type418 A) : ((_66562 = (term197 A)) = (term198 A _66562)) = ((_66562 = (term141 A)) = (term203 A _66562)).
Proof. exact (MK_COMB (@lem5106473 A _66562) (@lem5106479 A _66562)). Qed.
Lemma lem5106481 {A : Type'} (_66562 : type418 A) : (_66562 = (term141 A)) = (term203 A _66562).
Proof. exact (EQ_MP (@lem5106480 A _66562) (@lem5106467 A _66562)). Qed.
Lemma lem5106483 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term193 _3571 _3575 t)) = (term194 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5106484 {A : Type'} (s : type1402 A) (t : type1402 A) : (s = (term204 A t)) = (term205 A s t).
Proof. exact (@lem5106483 (A -> Prop) A s t). Qed.
Lemma lem5106485 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : ((_66562 lt2) = (term206 A lt2)) = (term207 A _66562 lt2).
Proof. exact (@lem5106484 A (_66562 lt2) (term143 A lt2)). Qed.
Lemma lem5106486 {A : Type'} (lt2 : type1402 A) (x : A) : (term145 A lt2 x) = (term146 A lt2 x).
Proof. exact (eq_refl (term145 A lt2 x)). Qed.
Lemma lem5106487 {A : Type'} (lt2 : type1402 A) : (term206 A lt2) = (term143 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5106486 A lt2 x)). Qed.
Lemma lem5106488 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term144 A _66562 lt2) = (term144 A _66562 lt2).
Proof. exact (eq_refl (term144 A _66562 lt2)). Qed.
Lemma lem5106489 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : ((_66562 lt2) = (term206 A lt2)) = ((_66562 lt2) = (term143 A lt2)).
Proof. exact (MK_COMB (@lem5106488 A _66562 lt2) (@lem5106487 A lt2)). Qed.
Lemma lem5106490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5106491 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term208 A _66562 lt2) = (term209 A _66562 lt2).
Proof. exact (MK_COMB (@lem5106490) (@lem5106489 A _66562 lt2)). Qed.
Lemma lem5106492 {A : Type'} (lt2 : type1402 A) (x : A) : (term145 A lt2 x) = (term146 A lt2 x).
Proof. exact (eq_refl (term145 A lt2 x)). Qed.
Lemma lem5106493 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term147 A _66562 lt2 x) = (term147 A _66562 lt2 x).
Proof. exact (eq_refl (term147 A _66562 lt2 x)). Qed.
Lemma lem5106494 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : ((_66562 lt2 x) = (term145 A lt2 x)) = ((_66562 lt2 x) = (term146 A lt2 x)).
Proof. exact (MK_COMB (@lem5106493 A _66562 lt2 x) (@lem5106492 A lt2 x)). Qed.
Lemma lem5106495 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term210 A _66562 lt2) = (term211 A _66562 lt2).
Proof. exact (fun_ext (fun x : A => @lem5106494 A _66562 lt2 x)). Qed.
Lemma lem5106496 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106497 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term207 A _66562 lt2) = (term212 A _66562 lt2).
Proof. exact (MK_COMB (@lem5106496 A) (@lem5106495 A _66562 lt2)). Qed.
Lemma lem5106498 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (((_66562 lt2) = (term206 A lt2)) = (term207 A _66562 lt2)) = (((_66562 lt2) = (term143 A lt2)) = (term212 A _66562 lt2)).
Proof. exact (MK_COMB (@lem5106491 A _66562 lt2) (@lem5106497 A _66562 lt2)). Qed.
Lemma lem5106499 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : ((_66562 lt2) = (term143 A lt2)) = (term212 A _66562 lt2).
Proof. exact (EQ_MP (@lem5106498 A _66562 lt2) (@lem5106485 A _66562 lt2)). Qed.
Lemma lem5106501 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term193 _3571 _3575 t)) = (term194 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5106502 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = (term213 A t)) = (term214 A s t).
Proof. exact (@lem5106501 Prop A s t). Qed.
Lemma lem5106503 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : ((_66562 lt2 x) = (term215 A lt2 x)) = (term216 A _66562 lt2 x).
Proof. exact (@lem5106502 A (_66562 lt2 x) (term146 A lt2 x)). Qed.
Lemma lem5106504 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term217 A lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term217 A lt2 x GEN_PVAR_227)). Qed.
Lemma lem5106505 {A : Type'} (lt2 : type1402 A) (x : A) : (term215 A lt2 x) = (term146 A lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5106504 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106506 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term147 A _66562 lt2 x) = (term147 A _66562 lt2 x).
Proof. exact (eq_refl (term147 A _66562 lt2 x)). Qed.
Lemma lem5106507 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : ((_66562 lt2 x) = (term215 A lt2 x)) = ((_66562 lt2 x) = (term146 A lt2 x)).
Proof. exact (MK_COMB (@lem5106506 A _66562 lt2 x) (@lem5106505 A lt2 x)). Qed.
Lemma lem5106508 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5106509 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term219 A _66562 lt2 x) = (term220 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5106508) (@lem5106507 A _66562 lt2 x)). Qed.
Lemma lem5106510 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term217 A lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term217 A lt2 x GEN_PVAR_227)). Qed.
Lemma lem5106511 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term221 A _66562 lt2 x GEN_PVAR_227) = (term221 A _66562 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term221 A _66562 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5106512 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((_66562 lt2 x GEN_PVAR_227) = (term217 A lt2 x GEN_PVAR_227)) = ((_66562 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)).
Proof. exact (MK_COMB (@lem5106511 A _66562 lt2 x GEN_PVAR_227) (@lem5106510 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106513 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term222 A _66562 lt2 x) = (term223 A _66562 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5106512 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106514 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106515 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term216 A _66562 lt2 x) = (term224 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5106514 A) (@lem5106513 A _66562 lt2 x)). Qed.
Lemma lem5106516 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (((_66562 lt2 x) = (term215 A lt2 x)) = (term216 A _66562 lt2 x)) = (((_66562 lt2 x) = (term146 A lt2 x)) = (term224 A _66562 lt2 x)).
Proof. exact (MK_COMB (@lem5106509 A _66562 lt2 x) (@lem5106515 A _66562 lt2 x)). Qed.
Lemma lem5106517 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : ((_66562 lt2 x) = (term146 A lt2 x)) = (term224 A _66562 lt2 x).
Proof. exact (EQ_MP (@lem5106516 A _66562 lt2 x) (@lem5106503 A _66562 lt2 x)). Qed.
Lemma lem5106518 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((_66562 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)) = ((_66562 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)).
Proof. exact (eq_refl ((_66562 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x))). Qed.
Lemma lem5106519 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term223 A _66562 lt2 x) = (term223 A _66562 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5106518 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106520 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106521 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term224 A _66562 lt2 x) = (term224 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5106520 A) (@lem5106519 A _66562 lt2 x)). Qed.
Lemma lem5106522 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : ((_66562 lt2 x) = (term146 A lt2 x)) = (term224 A _66562 lt2 x).
Proof. exact (TRANS (@lem5106517 A _66562 lt2 x) (@lem5106521 A _66562 lt2 x)). Qed.
Lemma lem5106523 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term211 A _66562 lt2) = (term225 A _66562 lt2).
Proof. exact (fun_ext (fun x : A => @lem5106522 A _66562 lt2 x)). Qed.
Lemma lem5106524 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106525 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term212 A _66562 lt2) = (term226 A _66562 lt2).
Proof. exact (MK_COMB (@lem5106524 A) (@lem5106523 A _66562 lt2)). Qed.
Lemma lem5106526 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : ((_66562 lt2) = (term143 A lt2)) = (term226 A _66562 lt2).
Proof. exact (TRANS (@lem5106499 A _66562 lt2) (@lem5106525 A _66562 lt2)). Qed.
Lemma lem5106527 {A : Type'} (_66562 : type418 A) : (term202 A _66562) = (term227 A _66562).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5106526 A _66562 lt2)). Qed.
Lemma lem5106528 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5106529 {A : Type'} (_66562 : type418 A) : (term203 A _66562) = (term228 A _66562).
Proof. exact (MK_COMB (@lem5106528 A) (@lem5106527 A _66562)). Qed.
Lemma lem5106530 {A : Type'} (_66562 : type418 A) : (_66562 = (term141 A)) = (term228 A _66562).
Proof. exact (TRANS (@lem5106481 A _66562) (@lem5106529 A _66562)). Qed.
Lemma lem5106531 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5106532 {A : Type'} (_66562 : type418 A) : (term179 A _66562) = (term229 A _66562).
Proof. exact (MK_COMB (@lem5106531) (@lem5106530 A _66562)). Qed.
Lemma lem5106533 {A : Type'} (_66562 : type418 A) : (term672 A _66562) = (term672 A _66562).
Proof. exact (eq_refl (term672 A _66562)). Qed.
Lemma lem5106534 {A : Type'} (_66562 : type418 A) : (term686 A _66562) = (term692 A _66562).
Proof. exact (MK_COMB (@lem5106532 A _66562) (@lem5106533 A _66562)). Qed.
Lemma lem5106535 {A : Type'} : (term688 A) = (term693 A).
Proof. exact (fun_ext (fun _66562 : type418 A => @lem5106534 A _66562)). Qed.
Lemma lem5106536 {A : Type'} : (@all ((A -> A -> Prop) -> A -> A -> Prop)) = (@all ((A -> A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem5106537 {A : Type'} : (term690 A) = (term694 A).
Proof. exact (MK_COMB (@lem5106536 A) (@lem5106535 A)). Qed.
Lemma lem5106538 {A : Type'} : (term678 A) = (term678 A).
Proof. exact (eq_refl (term678 A)). Qed.
Lemma lem5106539 {A : Type'} : ((term657 A) = (term690 A)) = ((term657 A) = (term694 A)).
Proof. exact (MK_COMB (@lem5106538 A) (@lem5106537 A)). Qed.
Lemma lem5106542 {A : Type'} : (term657 A) = (term694 A).
Proof. exact (EQ_MP (@lem5106539 A) (@lem5106463 A)). Qed.
Lemma lem5106543 {A : Type'} : (term656 A) = (term694 A).
Proof. exact (TRANS (@lem5106257 A) (@lem5106542 A)). Qed.
Lemma lem5106552 (m : nat) (n : nat) : (term658 m n) = (term658 m n).
Proof. exact (eq_refl (term658 m n)). Qed.
Lemma lem5106553 (m : nat) : (term659 m) = (term659 m).
Proof. exact (fun_ext (fun n : nat => @lem5106552 m n)). Qed.
Lemma lem5106554 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5106555 (m : nat) : (term660 m) = (term660 m).
Proof. exact (MK_COMB (@lem5106554) (@lem5106553 m)). Qed.
Lemma lem5106556 : term661 = term661.
Proof. exact (fun_ext (fun m : nat => @lem5106555 m)). Qed.
Lemma lem5106557 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5106558 : term636 = term636.
Proof. exact (MK_COMB (@lem5106557) (@lem5106556)). Qed.
Lemma lem5106559 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5106560 : term635 = term635.
Proof. exact (MK_COMB (@lem5106559) (@lem5106558)). Qed.
Lemma lem5106565 {A : Type'} (s : nat -> A) (x : nat) (y : nat) : (term662 A s x y) = (term662 A s x y).
Proof. exact (eq_refl (term662 A s x y)). Qed.
Lemma lem5106566 {A : Type'} (s : nat -> A) (x : nat) : (term663 A s x) = (term663 A s x).
Proof. exact (fun_ext (fun y : nat => @lem5106565 A s x y)). Qed.
Lemma lem5106567 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5106568 {A : Type'} (s : nat -> A) (x : nat) : (term664 A s x) = (term664 A s x).
Proof. exact (MK_COMB (@lem5106567) (@lem5106566 A s x)). Qed.
Lemma lem5106569 {A : Type'} (s : nat -> A) : (term665 A s) = (term665 A s).
Proof. exact (fun_ext (fun x : nat => @lem5106568 A s x)). Qed.
Lemma lem5106570 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5106571 {A : Type'} (s : nat -> A) : (term626 A s) = (term626 A s).
Proof. exact (MK_COMB (@lem5106570) (@lem5106569 A s)). Qed.
Lemma lem5106572 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5106573 {A : Type'} (s : nat -> A) : (term629 A s) = (term629 A s).
Proof. exact (MK_COMB (@lem5106572) (@lem5106571 A s)). Qed.
Lemma lem5106574 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5106575 {A : Type'} (s : nat -> A) : (term637 A s) = (term637 A s).
Proof. exact (MK_COMB (@lem5106574) (@lem5106573 A s)). Qed.
Lemma lem5106576 {A : Type'} (s : nat -> A) : (term639 A s) = (term639 A s).
Proof. exact (MK_COMB (@lem5106575 A s) (@lem5106560)). Qed.
Lemma lem5106581 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term104 A lt2 n s m) = (term104 A lt2 n s m).
Proof. exact (eq_refl (term104 A lt2 n s m)). Qed.
Lemma lem5106582 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term106 A lt2 s m) = (term106 A lt2 s m).
Proof. exact (fun_ext (fun n : nat => @lem5106581 A lt2 n s m)). Qed.
Lemma lem5106583 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5106584 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term108 A lt2 s m) = (term108 A lt2 s m).
Proof. exact (MK_COMB (@lem5106583) (@lem5106582 A lt2 s m)). Qed.
Lemma lem5106585 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term110 A lt2 s) = (term110 A lt2 s).
Proof. exact (fun_ext (fun m : nat => @lem5106584 A lt2 s m)). Qed.
Lemma lem5106586 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5106587 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term62 A lt2 s) = (term62 A lt2 s).
Proof. exact (MK_COMB (@lem5106586) (@lem5106585 A lt2 s)). Qed.
Lemma lem5106588 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5106589 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term640 A lt2 s) = (term640 A lt2 s).
Proof. exact (MK_COMB (@lem5106588) (@lem5106587 A lt2 s)). Qed.
Lemma lem5106590 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term642 A lt2 s) = (term642 A lt2 s).
Proof. exact (MK_COMB (@lem5106589 A lt2 s) (@lem5106576 A s)). Qed.
Lemma lem5106591 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term94 A lt2 s n) = (term94 A lt2 s n).
Proof. exact (eq_refl (term94 A lt2 s n)). Qed.
Lemma lem5106592 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term96 A lt2 s) = (term96 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5106591 A lt2 s n)). Qed.
Lemma lem5106593 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5106594 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term61 A lt2 s) = (term61 A lt2 s).
Proof. exact (MK_COMB (@lem5106593) (@lem5106592 A lt2 s)). Qed.
Lemma lem5106595 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5106596 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term122 A lt2 s) = (term122 A lt2 s).
Proof. exact (MK_COMB (@lem5106595) (@lem5106594 A lt2 s)). Qed.
Lemma lem5106597 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term644 A lt2 s) = (term644 A lt2 s).
Proof. exact (MK_COMB (@lem5106596 A lt2 s) (@lem5106590 A lt2 s)). Qed.
Lemma lem5106598 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term151 A _66562 lt2 x) = (term151 A _66562 lt2 x).
Proof. exact (eq_refl (term151 A _66562 lt2 x)). Qed.
Lemma lem5106599 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term153 A _66562 lt2) = (term153 A _66562 lt2).
Proof. exact (fun_ext (fun x : A => @lem5106598 A _66562 lt2 x)). Qed.
Lemma lem5106600 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106601 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term154 A _66562 lt2) = (term154 A _66562 lt2).
Proof. exact (MK_COMB (@lem5106600 A) (@lem5106599 A _66562 lt2)). Qed.
Lemma lem5106602 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5106603 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term155 A _66562 lt2) = (term155 A _66562 lt2).
Proof. exact (MK_COMB (@lem5106602) (@lem5106601 A _66562 lt2)). Qed.
Lemma lem5106604 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term666 A _66562 lt2 s) = (term666 A _66562 lt2 s).
Proof. exact (MK_COMB (@lem5106603 A _66562 lt2) (@lem5106597 A lt2 s)). Qed.
Lemma lem5106613 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term157 A y lt2 x z) = (term157 A y lt2 x z).
Proof. exact (eq_refl (term157 A y lt2 x z)). Qed.
Lemma lem5106614 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term158 A y lt2 x) = (term158 A y lt2 x).
Proof. exact (fun_ext (fun z : A => @lem5106613 A y lt2 x z)). Qed.
Lemma lem5106615 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106616 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term159 A y lt2 x) = (term159 A y lt2 x).
Proof. exact (MK_COMB (@lem5106615 A) (@lem5106614 A y lt2 x)). Qed.
Lemma lem5106617 {A : Type'} (lt2 : type1402 A) (x : A) : (term160 A lt2 x) = (term160 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5106616 A y lt2 x)). Qed.
Lemma lem5106618 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106619 {A : Type'} (lt2 : type1402 A) (x : A) : (term161 A lt2 x) = (term161 A lt2 x).
Proof. exact (MK_COMB (@lem5106618 A) (@lem5106617 A lt2 x)). Qed.
Lemma lem5106620 {A : Type'} (lt2 : type1402 A) : (term162 A lt2) = (term162 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5106619 A lt2 x)). Qed.
Lemma lem5106621 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106622 {A : Type'} (lt2 : type1402 A) : (term58 A lt2) = (term58 A lt2).
Proof. exact (MK_COMB (@lem5106621 A) (@lem5106620 A lt2)). Qed.
Lemma lem5106623 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5106624 {A : Type'} (lt2 : type1402 A) : (term128 A lt2) = (term128 A lt2).
Proof. exact (MK_COMB (@lem5106623) (@lem5106622 A lt2)). Qed.
Lemma lem5106625 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term667 A _66562 lt2 s) = (term667 A _66562 lt2 s).
Proof. exact (MK_COMB (@lem5106624 A lt2) (@lem5106604 A _66562 lt2 s)). Qed.
Lemma lem5106628 {A : Type'} (lt2 : type1402 A) (x : A) : (term164 A lt2 x) = (term164 A lt2 x).
Proof. exact (eq_refl (term164 A lt2 x)). Qed.
Lemma lem5106629 {A : Type'} (lt2 : type1402 A) : (term165 A lt2) = (term165 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5106628 A lt2 x)). Qed.
Lemma lem5106630 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106631 {A : Type'} (lt2 : type1402 A) : (term56 A lt2) = (term56 A lt2).
Proof. exact (MK_COMB (@lem5106630 A) (@lem5106629 A lt2)). Qed.
Lemma lem5106632 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5106633 {A : Type'} (lt2 : type1402 A) : (term131 A lt2) = (term131 A lt2).
Proof. exact (MK_COMB (@lem5106632) (@lem5106631 A lt2)). Qed.
Lemma lem5106634 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term668 A _66562 lt2 s) = (term668 A _66562 lt2 s).
Proof. exact (MK_COMB (@lem5106633 A lt2) (@lem5106625 A _66562 lt2 s)). Qed.
Lemma lem5106635 {A : Type'} (_66562 : type418 A) (s : nat -> A) : (term669 A _66562 s) = (term669 A _66562 s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5106634 A _66562 lt2 s)). Qed.
Lemma lem5106636 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5106637 {A : Type'} (_66562 : type418 A) (s : nat -> A) : (term670 A _66562 s) = (term670 A _66562 s).
Proof. exact (MK_COMB (@lem5106636 A) (@lem5106635 A _66562 s)). Qed.
Lemma lem5106638 {A : Type'} (_66562 : type418 A) : (term671 A _66562) = (term671 A _66562).
Proof. exact (fun_ext (fun s : nat -> A => @lem5106637 A _66562 s)). Qed.
Lemma lem5106639 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5106640 {A : Type'} (_66562 : type418 A) : (term672 A _66562) = (term672 A _66562).
Proof. exact (MK_COMB (@lem5106639 A) (@lem5106638 A _66562)). Qed.
Lemma lem5106641 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term233 A GEN_PVAR_227 lt2 x y) = (term233 A GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term233 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5106642 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term234 A GEN_PVAR_227 lt2 x) = (term234 A GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5106641 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5106643 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5106644 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term218 A GEN_PVAR_227 lt2 x) = (term218 A GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5106643 A) (@lem5106642 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106647 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term221 A _66562 lt2 x GEN_PVAR_227) = (term221 A _66562 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term221 A _66562 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5106648 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((_66562 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)) = ((_66562 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)).
Proof. exact (MK_COMB (@lem5106647 A _66562 lt2 x GEN_PVAR_227) (@lem5106644 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106649 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term223 A _66562 lt2 x) = (term223 A _66562 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5106648 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106650 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106651 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term224 A _66562 lt2 x) = (term224 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5106650 A) (@lem5106649 A _66562 lt2 x)). Qed.
Lemma lem5106652 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term225 A _66562 lt2) = (term225 A _66562 lt2).
Proof. exact (fun_ext (fun x : A => @lem5106651 A _66562 lt2 x)). Qed.
Lemma lem5106653 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106654 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term226 A _66562 lt2) = (term226 A _66562 lt2).
Proof. exact (MK_COMB (@lem5106653 A) (@lem5106652 A _66562 lt2)). Qed.
Lemma lem5106655 {A : Type'} (_66562 : type418 A) : (term227 A _66562) = (term227 A _66562).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5106654 A _66562 lt2)). Qed.
Lemma lem5106656 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5106657 {A : Type'} (_66562 : type418 A) : (term228 A _66562) = (term228 A _66562).
Proof. exact (MK_COMB (@lem5106656 A) (@lem5106655 A _66562)). Qed.
Lemma lem5106658 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5106659 {A : Type'} (_66562 : type418 A) : (term229 A _66562) = (term229 A _66562).
Proof. exact (MK_COMB (@lem5106658) (@lem5106657 A _66562)). Qed.
Lemma lem5106660 {A : Type'} (_66562 : type418 A) : (term692 A _66562) = (term692 A _66562).
Proof. exact (MK_COMB (@lem5106659 A _66562) (@lem5106640 A _66562)). Qed.
Lemma lem5106661 {A : Type'} : (term693 A) = (term693 A).
Proof. exact (fun_ext (fun _66562 : type418 A => @lem5106660 A _66562)). Qed.
Lemma lem5106662 {A : Type'} : (@all ((A -> A -> Prop) -> A -> A -> Prop)) = (@all ((A -> A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem5106663 {A : Type'} : (term694 A) = (term694 A).
Proof. exact (MK_COMB (@lem5106662 A) (@lem5106661 A)). Qed.
Lemma lem5106806 {A : Type'} : (term656 A) = (term694 A).
Proof. exact (TRANS (@lem5106543 A) (@lem5106663 A)). Qed.
Lemma lem5106807 {A : Type'} : (term694 A) = (term656 A).
Proof. exact (SYM (@lem5106806 A)). Qed.
Lemma lem5106808 {A : Type'} (_66562 : type418 A) (h1 : term228 A _66562) : term228 A _66562.
Proof. exact (h1). Qed.
Lemma lem5106809 {A : Type'} (lt2 : type1402 A) (h1 : term56 A lt2) : term56 A lt2.
Proof. exact (h1). Qed.
Lemma lem5106813 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term62 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem5106814 {A : Type'} (s : nat -> A) (h1 : term629 A s) : term629 A s.
Proof. exact (h1). Qed.
Lemma lem5106815 (h1 : term636) : term636.
Proof. exact (h1). Qed.
Lemma lem5106819 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term233 A GEN_PVAR_227 lt2 x y) = (term233 A GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term233 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5106820 {A : Type'} (P : A -> Prop) : (term235 A P) = (term236 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5106821 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term237 A GEN_PVAR_227 lt2 x) = (term238 A GEN_PVAR_227 lt2 x).
Proof. exact (@lem5106820 A (term234 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106822 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term239 A GEN_PVAR_227 lt2 x y) = (term233 A GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term239 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5106823 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5106825 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term240 A GEN_PVAR_227 lt2 x y) = (term241 A GEN_PVAR_227 lt2 x y).
Proof. exact (MK_COMB (@lem5106823) (@lem5106822 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5106826 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term242 A GEN_PVAR_227 lt2 x) = (term243 A GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5106825 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5106827 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106828 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term238 A GEN_PVAR_227 lt2 x) = (term244 A GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5106827 A) (@lem5106826 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106829 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term237 A GEN_PVAR_227 lt2 x) = (term244 A GEN_PVAR_227 lt2 x).
Proof. exact (TRANS (@lem5106821 A GEN_PVAR_227 lt2 x) (@lem5106828 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106830 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term234 A GEN_PVAR_227 lt2 x) = (term234 A GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5106819 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5106831 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5106832 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term218 A GEN_PVAR_227 lt2 x) = (term218 A GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5106831 A) (@lem5106830 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106834 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term245 A _66562 lt2 x GEN_PVAR_227) = (term245 A _66562 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term245 A _66562 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5106835 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term246 A _66562 GEN_PVAR_227 lt2 x) = (term246 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5106834 A _66562 lt2 x GEN_PVAR_227) (@lem5106832 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106837 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term247 A _66562 lt2 x GEN_PVAR_227) = (term247 A _66562 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term247 A _66562 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5106838 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term248 A _66562 GEN_PVAR_227 lt2 x) = (term249 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5106837 A _66562 lt2 x GEN_PVAR_227) (@lem5106829 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5106840 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term250 A _66562 GEN_PVAR_227 lt2 x) = (term251 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5106839) (@lem5106838 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106841 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term252 A _66562 GEN_PVAR_227 lt2 x) = (term253 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5106840 A _66562 GEN_PVAR_227 lt2 x) (@lem5106835 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106842 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((_66562 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)) = (term252 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (@lem17784 (_66562 lt2 x GEN_PVAR_227) (term218 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106843 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((_66562 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)) = (term253 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (TRANS (@lem5106842 A _66562 GEN_PVAR_227 lt2 x) (@lem5106841 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106844 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term223 A _66562 lt2 x) = (term254 A _66562 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5106843 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106845 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106846 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term224 A _66562 lt2 x) = (term255 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5106845 A) (@lem5106844 A _66562 lt2 x)). Qed.
Lemma lem5106847 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term225 A _66562 lt2) = (term256 A _66562 lt2).
Proof. exact (fun_ext (fun x : A => @lem5106846 A _66562 lt2 x)). Qed.
Lemma lem5106848 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106849 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term226 A _66562 lt2) = (term257 A _66562 lt2).
Proof. exact (MK_COMB (@lem5106848 A) (@lem5106847 A _66562 lt2)). Qed.
Lemma lem5106850 {A : Type'} (_66562 : type418 A) : (term227 A _66562) = (term258 A _66562).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5106849 A _66562 lt2)). Qed.
Lemma lem5106851 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5106852 {A : Type'} (_66562 : type418 A) : (term228 A _66562) = (term259 A _66562).
Proof. exact (MK_COMB (@lem5106851 A) (@lem5106850 A _66562)). Qed.
Lemma lem5106862 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5106863 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (@lem5106862 A P Q). Qed.
Lemma lem5106864 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term262 A _66562 lt2 x) = (term263 A _66562 lt2 x).
Proof. exact (@lem5106863 A (term264 A _66562 lt2 x) (term265 A _66562 lt2 x)). Qed.
Lemma lem5106865 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term266 A _66562 lt2 x GEN_PVAR_227) = (term249 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term266 A _66562 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5106866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5106867 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term267 A _66562 lt2 x GEN_PVAR_227) = (term251 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5106866) (@lem5106865 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106868 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term268 A _66562 lt2 x GEN_PVAR_227) = (term246 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term268 A _66562 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5106869 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term269 A _66562 lt2 x GEN_PVAR_227) = (term253 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5106867 A _66562 GEN_PVAR_227 lt2 x) (@lem5106868 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106870 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term270 A _66562 lt2 x) = (term254 A _66562 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5106869 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106871 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106872 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term262 A _66562 lt2 x) = (term255 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5106871 A) (@lem5106870 A _66562 lt2 x)). Qed.
Lemma lem5106873 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5106874 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term271 A _66562 lt2 x) = (term272 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5106873) (@lem5106872 A _66562 lt2 x)). Qed.
Lemma lem5106875 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term266 A _66562 lt2 x GEN_PVAR_227) = (term249 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term266 A _66562 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5106876 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term273 A _66562 lt2 x) = (term264 A _66562 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5106875 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106877 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106878 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term274 A _66562 lt2 x) = (term275 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5106877 A) (@lem5106876 A _66562 lt2 x)). Qed.
Lemma lem5106879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5106880 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term276 A _66562 lt2 x) = (term277 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5106879) (@lem5106878 A _66562 lt2 x)). Qed.
Lemma lem5106881 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term268 A _66562 lt2 x GEN_PVAR_227) = (term246 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term268 A _66562 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5106882 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term278 A _66562 lt2 x) = (term265 A _66562 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5106881 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5106883 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106884 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term279 A _66562 lt2 x) = (term280 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5106883 A) (@lem5106882 A _66562 lt2 x)). Qed.
Lemma lem5106885 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term263 A _66562 lt2 x) = (term281 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5106880 A _66562 lt2 x) (@lem5106884 A _66562 lt2 x)). Qed.
Lemma lem5106886 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : ((term262 A _66562 lt2 x) = (term263 A _66562 lt2 x)) = ((term255 A _66562 lt2 x) = (term281 A _66562 lt2 x)).
Proof. exact (MK_COMB (@lem5106874 A _66562 lt2 x) (@lem5106885 A _66562 lt2 x)). Qed.
Lemma lem5106887 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term255 A _66562 lt2 x) = (term281 A _66562 lt2 x).
Proof. exact (EQ_MP (@lem5106886 A _66562 lt2 x) (@lem5106864 A _66562 lt2 x)). Qed.
Lemma lem5106992 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term256 A _66562 lt2) = (term282 A _66562 lt2).
Proof. exact (fun_ext (fun x : A => @lem5106887 A _66562 lt2 x)). Qed.
Lemma lem5106993 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5106994 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term257 A _66562 lt2) = (term283 A _66562 lt2).
Proof. exact (MK_COMB (@lem5106993 A) (@lem5106992 A _66562 lt2)). Qed.
Lemma lem5106996 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5106997 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (@lem5106996 A P Q). Qed.
Lemma lem5106998 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term284 A _66562 lt2) = (term285 A _66562 lt2).
Proof. exact (@lem5106997 A (term286 A _66562 lt2) (term287 A _66562 lt2)). Qed.
Lemma lem5106999 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term288 A _66562 lt2 x) = (term275 A _66562 lt2 x).
Proof. exact (eq_refl (term288 A _66562 lt2 x)). Qed.
Lemma lem5107000 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5107001 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term289 A _66562 lt2 x) = (term277 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5107000) (@lem5106999 A _66562 lt2 x)). Qed.
Lemma lem5107002 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term290 A _66562 lt2 x) = (term280 A _66562 lt2 x).
Proof. exact (eq_refl (term290 A _66562 lt2 x)). Qed.
Lemma lem5107003 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term291 A _66562 lt2 x) = (term281 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5107001 A _66562 lt2 x) (@lem5107002 A _66562 lt2 x)). Qed.
Lemma lem5107004 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term292 A _66562 lt2) = (term282 A _66562 lt2).
Proof. exact (fun_ext (fun x : A => @lem5107003 A _66562 lt2 x)). Qed.
Lemma lem5107005 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5107006 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term284 A _66562 lt2) = (term283 A _66562 lt2).
Proof. exact (MK_COMB (@lem5107005 A) (@lem5107004 A _66562 lt2)). Qed.
Lemma lem5107007 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5107008 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term293 A _66562 lt2) = (term294 A _66562 lt2).
Proof. exact (MK_COMB (@lem5107007) (@lem5107006 A _66562 lt2)). Qed.
Lemma lem5107009 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term288 A _66562 lt2 x) = (term275 A _66562 lt2 x).
Proof. exact (eq_refl (term288 A _66562 lt2 x)). Qed.
Lemma lem5107010 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term295 A _66562 lt2) = (term286 A _66562 lt2).
Proof. exact (fun_ext (fun x : A => @lem5107009 A _66562 lt2 x)). Qed.
Lemma lem5107011 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5107012 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term296 A _66562 lt2) = (term297 A _66562 lt2).
Proof. exact (MK_COMB (@lem5107011 A) (@lem5107010 A _66562 lt2)). Qed.
Lemma lem5107013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5107014 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term298 A _66562 lt2) = (term299 A _66562 lt2).
Proof. exact (MK_COMB (@lem5107013) (@lem5107012 A _66562 lt2)). Qed.
Lemma lem5107015 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term290 A _66562 lt2 x) = (term280 A _66562 lt2 x).
Proof. exact (eq_refl (term290 A _66562 lt2 x)). Qed.
Lemma lem5107016 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term300 A _66562 lt2) = (term287 A _66562 lt2).
Proof. exact (fun_ext (fun x : A => @lem5107015 A _66562 lt2 x)). Qed.
Lemma lem5107017 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5107018 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term301 A _66562 lt2) = (term302 A _66562 lt2).
Proof. exact (MK_COMB (@lem5107017 A) (@lem5107016 A _66562 lt2)). Qed.
Lemma lem5107019 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term285 A _66562 lt2) = (term303 A _66562 lt2).
Proof. exact (MK_COMB (@lem5107014 A _66562 lt2) (@lem5107018 A _66562 lt2)). Qed.
Lemma lem5107020 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : ((term284 A _66562 lt2) = (term285 A _66562 lt2)) = ((term283 A _66562 lt2) = (term303 A _66562 lt2)).
Proof. exact (MK_COMB (@lem5107008 A _66562 lt2) (@lem5107019 A _66562 lt2)). Qed.
Lemma lem5107021 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term283 A _66562 lt2) = (term303 A _66562 lt2).
Proof. exact (EQ_MP (@lem5107020 A _66562 lt2) (@lem5106998 A _66562 lt2)). Qed.
Lemma lem5107134 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term257 A _66562 lt2) = (term303 A _66562 lt2).
Proof. exact (TRANS (@lem5106994 A _66562 lt2) (@lem5107021 A _66562 lt2)). Qed.
Lemma lem5107135 {A : Type'} (_66562 : type418 A) : (term258 A _66562) = (term304 A _66562).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5107134 A _66562 lt2)). Qed.
Lemma lem5107136 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5107137 {A : Type'} (_66562 : type418 A) : (term259 A _66562) = (term305 A _66562).
Proof. exact (MK_COMB (@lem5107136 A) (@lem5107135 A _66562)). Qed.
Lemma lem5107139 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5107140 {A : Type'} (P : type421 A) (Q : type421 A) : (term306 A P Q) = (term307 A P Q).
Proof. exact (@lem5107139 (type1402 A) P Q). Qed.
Lemma lem5107141 {A : Type'} (_66562 : type418 A) : (term308 A _66562) = (term309 A _66562).
Proof. exact (@lem5107140 A (term310 A _66562) (term311 A _66562)). Qed.
Lemma lem5107142 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term312 A _66562 lt2) = (term297 A _66562 lt2).
Proof. exact (eq_refl (term312 A _66562 lt2)). Qed.
Lemma lem5107143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5107144 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term313 A _66562 lt2) = (term299 A _66562 lt2).
Proof. exact (MK_COMB (@lem5107143) (@lem5107142 A _66562 lt2)). Qed.
Lemma lem5107145 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term314 A _66562 lt2) = (term302 A _66562 lt2).
Proof. exact (eq_refl (term314 A _66562 lt2)). Qed.
Lemma lem5107146 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term315 A _66562 lt2) = (term303 A _66562 lt2).
Proof. exact (MK_COMB (@lem5107144 A _66562 lt2) (@lem5107145 A _66562 lt2)). Qed.
Lemma lem5107147 {A : Type'} (_66562 : type418 A) : (term316 A _66562) = (term304 A _66562).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5107146 A _66562 lt2)). Qed.
Lemma lem5107148 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5107149 {A : Type'} (_66562 : type418 A) : (term308 A _66562) = (term305 A _66562).
Proof. exact (MK_COMB (@lem5107148 A) (@lem5107147 A _66562)). Qed.
Lemma lem5107150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5107151 {A : Type'} (_66562 : type418 A) : (term317 A _66562) = (term318 A _66562).
Proof. exact (MK_COMB (@lem5107150) (@lem5107149 A _66562)). Qed.
Lemma lem5107152 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term312 A _66562 lt2) = (term297 A _66562 lt2).
Proof. exact (eq_refl (term312 A _66562 lt2)). Qed.
Lemma lem5107153 {A : Type'} (_66562 : type418 A) : (term319 A _66562) = (term310 A _66562).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5107152 A _66562 lt2)). Qed.
Lemma lem5107154 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5107155 {A : Type'} (_66562 : type418 A) : (term320 A _66562) = (term321 A _66562).
Proof. exact (MK_COMB (@lem5107154 A) (@lem5107153 A _66562)). Qed.
Lemma lem5107156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5107157 {A : Type'} (_66562 : type418 A) : (term322 A _66562) = (term323 A _66562).
Proof. exact (MK_COMB (@lem5107156) (@lem5107155 A _66562)). Qed.
Lemma lem5107158 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term314 A _66562 lt2) = (term302 A _66562 lt2).
Proof. exact (eq_refl (term314 A _66562 lt2)). Qed.
Lemma lem5107159 {A : Type'} (_66562 : type418 A) : (term324 A _66562) = (term311 A _66562).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5107158 A _66562 lt2)). Qed.
Lemma lem5107160 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5107161 {A : Type'} (_66562 : type418 A) : (term325 A _66562) = (term326 A _66562).
Proof. exact (MK_COMB (@lem5107160 A) (@lem5107159 A _66562)). Qed.
Lemma lem5107162 {A : Type'} (_66562 : type418 A) : (term309 A _66562) = (term327 A _66562).
Proof. exact (MK_COMB (@lem5107157 A _66562) (@lem5107161 A _66562)). Qed.
Lemma lem5107163 {A : Type'} (_66562 : type418 A) : ((term308 A _66562) = (term309 A _66562)) = ((term305 A _66562) = (term327 A _66562)).
Proof. exact (MK_COMB (@lem5107151 A _66562) (@lem5107162 A _66562)). Qed.
Lemma lem5107164 {A : Type'} (_66562 : type418 A) : (term305 A _66562) = (term327 A _66562).
Proof. exact (EQ_MP (@lem5107163 A _66562) (@lem5107141 A _66562)). Qed.
Lemma lem5107285 {A : Type'} (_66562 : type418 A) : (term259 A _66562) = (term327 A _66562).
Proof. exact (TRANS (@lem5107137 A _66562) (@lem5107164 A _66562)). Qed.
Lemma lem5107287 {A : Type'} (P : Prop) (Q : A -> Prop) : (term328 A P Q) = (term329 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5107288 {A : Type'} (P : Prop) (Q : A -> Prop) : (term328 A P Q) = (term329 A P Q).
Proof. exact (@lem5107287 A P Q). Qed.
Lemma lem5107289 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term330 A _66562 GEN_PVAR_227 lt2 x) = (term331 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (@lem5107288 A (term332 A _66562 lt2 x GEN_PVAR_227) (term234 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5107290 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term239 A GEN_PVAR_227 lt2 x y) = (term233 A GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term239 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5107291 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term333 A GEN_PVAR_227 lt2 x) = (term234 A GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5107290 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5107292 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5107293 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term334 A GEN_PVAR_227 lt2 x) = (term218 A GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5107292 A) (@lem5107291 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5107294 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term245 A _66562 lt2 x GEN_PVAR_227) = (term245 A _66562 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term245 A _66562 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5107295 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term330 A _66562 GEN_PVAR_227 lt2 x) = (term246 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5107294 A _66562 lt2 x GEN_PVAR_227) (@lem5107293 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5107296 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5107297 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term335 A _66562 GEN_PVAR_227 lt2 x) = (term336 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5107296) (@lem5107295 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5107298 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term239 A GEN_PVAR_227 lt2 x y) = (term233 A GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term239 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5107299 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term245 A _66562 lt2 x GEN_PVAR_227) = (term245 A _66562 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term245 A _66562 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5107300 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term337 A _66562 GEN_PVAR_227 lt2 x y) = (term338 A _66562 GEN_PVAR_227 lt2 x y).
Proof. exact (MK_COMB (@lem5107299 A _66562 lt2 x GEN_PVAR_227) (@lem5107298 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5107301 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term339 A _66562 GEN_PVAR_227 lt2 x) = (term340 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5107300 A _66562 GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5107302 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5107303 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term331 A _66562 GEN_PVAR_227 lt2 x) = (term341 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5107302 A) (@lem5107301 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5107304 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((term330 A _66562 GEN_PVAR_227 lt2 x) = (term331 A _66562 GEN_PVAR_227 lt2 x)) = ((term246 A _66562 GEN_PVAR_227 lt2 x) = (term341 A _66562 GEN_PVAR_227 lt2 x)).
Proof. exact (MK_COMB (@lem5107297 A _66562 GEN_PVAR_227 lt2 x) (@lem5107303 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5107305 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term246 A _66562 GEN_PVAR_227 lt2 x) = (term341 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (EQ_MP (@lem5107304 A _66562 GEN_PVAR_227 lt2 x) (@lem5107289 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5107306 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term265 A _66562 lt2 x) = (term342 A _66562 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5107305 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5107307 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5107308 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term280 A _66562 lt2 x) = (term343 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5107307 A) (@lem5107306 A _66562 lt2 x)). Qed.
Lemma lem5107310 {A B : Type'} (P : type1413 A B) : (term344 A B P) = (term345 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5107311 {A : Type'} (P : type1402 A) : (term346 A P) = (term347 A P).
Proof. exact (@lem5107310 A A P). Qed.
Lemma lem5107312 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term348 A _66562 lt2 x) = (term349 A _66562 lt2 x).
Proof. exact (@lem5107311 A (term350 A _66562 lt2 x)). Qed.
Lemma lem5107313 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term351 A _66562 lt2 x GEN_PVAR_227) = (term340 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term351 A _66562 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5107314 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5107315 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term352 A _66562 lt2 x GEN_PVAR_227 y) = (term353 A _66562 GEN_PVAR_227 lt2 x y).
Proof. exact (MK_COMB (@lem5107313 A _66562 GEN_PVAR_227 lt2 x) (@lem5107314 A y)). Qed.
Lemma lem5107316 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term353 A _66562 GEN_PVAR_227 lt2 x y) = (term338 A _66562 GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term353 A _66562 GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5107317 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term352 A _66562 lt2 x GEN_PVAR_227 y) = (term338 A _66562 GEN_PVAR_227 lt2 x y).
Proof. exact (TRANS (@lem5107315 A _66562 GEN_PVAR_227 lt2 x y) (@lem5107316 A _66562 GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5107318 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term354 A _66562 lt2 x GEN_PVAR_227) = (term340 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5107317 A _66562 GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5107319 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5107320 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term355 A _66562 lt2 x GEN_PVAR_227) = (term341 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5107319 A) (@lem5107318 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5107321 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term356 A _66562 lt2 x) = (term342 A _66562 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5107320 A _66562 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5107322 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5107323 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term348 A _66562 lt2 x) = (term343 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5107322 A) (@lem5107321 A _66562 lt2 x)). Qed.
Lemma lem5107324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5107325 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term357 A _66562 lt2 x) = (term358 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5107324) (@lem5107323 A _66562 lt2 x)). Qed.
Lemma lem5107326 {A : Type'} (_66562 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term351 A _66562 lt2 x GEN_PVAR_227) = (term340 A _66562 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term351 A _66562 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5107327 {A : Type'} (y : A -> A) (GEN_PVAR_227 : A) : (y GEN_PVAR_227) = (y GEN_PVAR_227).
Proof. exact (eq_refl (y GEN_PVAR_227)). Qed.
Lemma lem5107328 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) (GEN_PVAR_227 : A) : (term359 A _66562 lt2 x y GEN_PVAR_227) = (term360 A _66562 lt2 x y GEN_PVAR_227).
Proof. exact (MK_COMB (@lem5107326 A _66562 GEN_PVAR_227 lt2 x) (@lem5107327 A y GEN_PVAR_227)). Qed.
Lemma lem5107329 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) (GEN_PVAR_227 : A) : (term360 A _66562 lt2 x y GEN_PVAR_227) = (term361 A _66562 lt2 x y GEN_PVAR_227).
Proof. exact (eq_refl (term360 A _66562 lt2 x y GEN_PVAR_227)). Qed.
Lemma lem5107330 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) (GEN_PVAR_227 : A) : (term359 A _66562 lt2 x y GEN_PVAR_227) = (term361 A _66562 lt2 x y GEN_PVAR_227).
Proof. exact (TRANS (@lem5107328 A _66562 lt2 x y GEN_PVAR_227) (@lem5107329 A _66562 lt2 x y GEN_PVAR_227)). Qed.
Lemma lem5107331 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) : (term362 A _66562 lt2 x y) = (term363 A _66562 lt2 x y).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5107330 A _66562 lt2 x y GEN_PVAR_227)). Qed.
Lemma lem5107332 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5107333 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) : (term364 A _66562 lt2 x y) = (term365 A _66562 lt2 x y).
Proof. exact (MK_COMB (@lem5107332 A) (@lem5107331 A _66562 lt2 x y)). Qed.
Lemma lem5107334 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term366 A _66562 lt2 x) = (term367 A _66562 lt2 x).
Proof. exact (fun_ext (fun y : A -> A => @lem5107333 A _66562 lt2 x y)). Qed.
Lemma lem5107335 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem5107336 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term349 A _66562 lt2 x) = (term368 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5107335 A) (@lem5107334 A _66562 lt2 x)). Qed.
Lemma lem5107337 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : ((term348 A _66562 lt2 x) = (term349 A _66562 lt2 x)) = ((term343 A _66562 lt2 x) = (term368 A _66562 lt2 x)).
Proof. exact (MK_COMB (@lem5107325 A _66562 lt2 x) (@lem5107336 A _66562 lt2 x)). Qed.
Lemma lem5107338 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term343 A _66562 lt2 x) = (term368 A _66562 lt2 x).
Proof. exact (EQ_MP (@lem5107337 A _66562 lt2 x) (@lem5107312 A _66562 lt2 x)). Qed.
Lemma lem5107339 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term280 A _66562 lt2 x) = (term368 A _66562 lt2 x).
Proof. exact (TRANS (@lem5107308 A _66562 lt2 x) (@lem5107338 A _66562 lt2 x)). Qed.
Lemma lem5107340 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term287 A _66562 lt2) = (term369 A _66562 lt2).
Proof. exact (fun_ext (fun x : A => @lem5107339 A _66562 lt2 x)). Qed.
Lemma lem5107341 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5107342 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term302 A _66562 lt2) = (term370 A _66562 lt2).
Proof. exact (MK_COMB (@lem5107341 A) (@lem5107340 A _66562 lt2)). Qed.
Lemma lem5107344 {A B : Type'} (P : type1413 A B) : (term344 A B P) = (term345 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5107345 {A : Type'} (P : type1359 A) : (term371 A P) = (term372 A P).
Proof. exact (@lem5107344 A (A -> A) P). Qed.
Lemma lem5107346 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term373 A _66562 lt2) = (term374 A _66562 lt2).
Proof. exact (@lem5107345 A (term375 A _66562 lt2)). Qed.
Lemma lem5107347 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term376 A _66562 lt2 x) = (term367 A _66562 lt2 x).
Proof. exact (eq_refl (term376 A _66562 lt2 x)). Qed.
Lemma lem5107348 {A : Type'} (y : A -> A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5107349 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) : (term377 A _66562 lt2 x y) = (term378 A _66562 lt2 x y).
Proof. exact (MK_COMB (@lem5107347 A _66562 lt2 x) (@lem5107348 A y)). Qed.
Lemma lem5107350 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) : (term378 A _66562 lt2 x y) = (term365 A _66562 lt2 x y).
Proof. exact (eq_refl (term378 A _66562 lt2 x y)). Qed.
Lemma lem5107351 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) : (term377 A _66562 lt2 x y) = (term365 A _66562 lt2 x y).
Proof. exact (TRANS (@lem5107349 A _66562 lt2 x y) (@lem5107350 A _66562 lt2 x y)). Qed.
Lemma lem5107352 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term379 A _66562 lt2 x) = (term367 A _66562 lt2 x).
Proof. exact (fun_ext (fun y : A -> A => @lem5107351 A _66562 lt2 x y)). Qed.
Lemma lem5107353 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem5107354 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term380 A _66562 lt2 x) = (term368 A _66562 lt2 x).
Proof. exact (MK_COMB (@lem5107353 A) (@lem5107352 A _66562 lt2 x)). Qed.
Lemma lem5107355 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term381 A _66562 lt2) = (term369 A _66562 lt2).
Proof. exact (fun_ext (fun x : A => @lem5107354 A _66562 lt2 x)). Qed.
Lemma lem5107356 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5107357 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term373 A _66562 lt2) = (term370 A _66562 lt2).
Proof. exact (MK_COMB (@lem5107356 A) (@lem5107355 A _66562 lt2)). Qed.
Lemma lem5107358 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5107359 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term382 A _66562 lt2) = (term383 A _66562 lt2).
Proof. exact (MK_COMB (@lem5107358) (@lem5107357 A _66562 lt2)). Qed.
Lemma lem5107360 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (x : A) : (term376 A _66562 lt2 x) = (term367 A _66562 lt2 x).
Proof. exact (eq_refl (term376 A _66562 lt2 x)). Qed.
Lemma lem5107361 {A : Type'} (y : type1400 A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem5107362 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (y : type1400 A) (x : A) : (term384 A _66562 lt2 y x) = (term385 A _66562 lt2 y x).
Proof. exact (MK_COMB (@lem5107360 A _66562 lt2 x) (@lem5107361 A y x)). Qed.
Lemma lem5107363 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (y : type1400 A) (x : A) : (term385 A _66562 lt2 y x) = (term386 A _66562 lt2 y x).
Proof. exact (eq_refl (term385 A _66562 lt2 y x)). Qed.
Lemma lem5107364 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (y : type1400 A) (x : A) : (term384 A _66562 lt2 y x) = (term386 A _66562 lt2 y x).
Proof. exact (TRANS (@lem5107362 A _66562 lt2 y x) (@lem5107363 A _66562 lt2 y x)). Qed.
Lemma lem5107365 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (y : type1400 A) : (term387 A _66562 lt2 y) = (term388 A _66562 lt2 y).
Proof. exact (fun_ext (fun x : A => @lem5107364 A _66562 lt2 y x)). Qed.
Lemma lem5107366 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5107367 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (y : type1400 A) : (term389 A _66562 lt2 y) = (term390 A _66562 lt2 y).
Proof. exact (MK_COMB (@lem5107366 A) (@lem5107365 A _66562 lt2 y)). Qed.
Lemma lem5107368 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term391 A _66562 lt2) = (term392 A _66562 lt2).
Proof. exact (fun_ext (fun y : type1400 A => @lem5107367 A _66562 lt2 y)). Qed.
Lemma lem5107369 {A : Type'} : (@ex (A -> A -> A)) = (@ex (A -> A -> A)).
Proof. exact (eq_refl (@ex (A -> A -> A))). Qed.
Lemma lem5107370 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term374 A _66562 lt2) = (term393 A _66562 lt2).
Proof. exact (MK_COMB (@lem5107369 A) (@lem5107368 A _66562 lt2)). Qed.
Lemma lem5107371 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : ((term373 A _66562 lt2) = (term374 A _66562 lt2)) = ((term370 A _66562 lt2) = (term393 A _66562 lt2)).
Proof. exact (MK_COMB (@lem5107359 A _66562 lt2) (@lem5107370 A _66562 lt2)). Qed.
Lemma lem5107372 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term370 A _66562 lt2) = (term393 A _66562 lt2).
Proof. exact (EQ_MP (@lem5107371 A _66562 lt2) (@lem5107346 A _66562 lt2)). Qed.
Lemma lem5107373 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term302 A _66562 lt2) = (term393 A _66562 lt2).
Proof. exact (TRANS (@lem5107342 A _66562 lt2) (@lem5107372 A _66562 lt2)). Qed.
Lemma lem5107374 {A : Type'} (_66562 : type418 A) : (term311 A _66562) = (term394 A _66562).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5107373 A _66562 lt2)). Qed.
Lemma lem5107375 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5107376 {A : Type'} (_66562 : type418 A) : (term326 A _66562) = (term395 A _66562).
Proof. exact (MK_COMB (@lem5107375 A) (@lem5107374 A _66562)). Qed.
Lemma lem5107378 {A B : Type'} (P : type1413 A B) : (term344 A B P) = (term345 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5107379 {A : Type'} (P : type412 A) : (term396 A P) = (term397 A P).
Proof. exact (@lem5107378 (type1402 A) (type1400 A) P). Qed.
Lemma lem5107380 {A : Type'} (_66562 : type418 A) : (term398 A _66562) = (term399 A _66562).
Proof. exact (@lem5107379 A (term400 A _66562)). Qed.
Lemma lem5107381 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term401 A _66562 lt2) = (term392 A _66562 lt2).
Proof. exact (eq_refl (term401 A _66562 lt2)). Qed.
Lemma lem5107382 {A : Type'} (y : type1400 A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5107383 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (y : type1400 A) : (term402 A _66562 lt2 y) = (term403 A _66562 lt2 y).
Proof. exact (MK_COMB (@lem5107381 A _66562 lt2) (@lem5107382 A y)). Qed.
Lemma lem5107384 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (y : type1400 A) : (term403 A _66562 lt2 y) = (term390 A _66562 lt2 y).
Proof. exact (eq_refl (term403 A _66562 lt2 y)). Qed.
Lemma lem5107385 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (y : type1400 A) : (term402 A _66562 lt2 y) = (term390 A _66562 lt2 y).
Proof. exact (TRANS (@lem5107383 A _66562 lt2 y) (@lem5107384 A _66562 lt2 y)). Qed.
Lemma lem5107386 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term404 A _66562 lt2) = (term392 A _66562 lt2).
Proof. exact (fun_ext (fun y : type1400 A => @lem5107385 A _66562 lt2 y)). Qed.
Lemma lem5107387 {A : Type'} : (@ex (A -> A -> A)) = (@ex (A -> A -> A)).
Proof. exact (eq_refl (@ex (A -> A -> A))). Qed.
Lemma lem5107388 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term405 A _66562 lt2) = (term393 A _66562 lt2).
Proof. exact (MK_COMB (@lem5107387 A) (@lem5107386 A _66562 lt2)). Qed.
Lemma lem5107389 {A : Type'} (_66562 : type418 A) : (term406 A _66562) = (term394 A _66562).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5107388 A _66562 lt2)). Qed.
Lemma lem5107390 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5107391 {A : Type'} (_66562 : type418 A) : (term398 A _66562) = (term395 A _66562).
Proof. exact (MK_COMB (@lem5107390 A) (@lem5107389 A _66562)). Qed.
Lemma lem5107392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5107393 {A : Type'} (_66562 : type418 A) : (term407 A _66562) = (term408 A _66562).
Proof. exact (MK_COMB (@lem5107392) (@lem5107391 A _66562)). Qed.
Lemma lem5107394 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) : (term401 A _66562 lt2) = (term392 A _66562 lt2).
Proof. exact (eq_refl (term401 A _66562 lt2)). Qed.
Lemma lem5107395 {A : Type'} (y : type417 A) (lt2 : type1402 A) : (y lt2) = (y lt2).
Proof. exact (eq_refl (y lt2)). Qed.
Lemma lem5107396 {A : Type'} (_66562 : type418 A) (y : type417 A) (lt2 : type1402 A) : (term409 A _66562 y lt2) = (term410 A _66562 y lt2).
Proof. exact (MK_COMB (@lem5107394 A _66562 lt2) (@lem5107395 A y lt2)). Qed.
Lemma lem5107397 {A : Type'} (_66562 : type418 A) (y : type417 A) (lt2 : type1402 A) : (term410 A _66562 y lt2) = (term411 A _66562 y lt2).
Proof. exact (eq_refl (term410 A _66562 y lt2)). Qed.
Lemma lem5107398 {A : Type'} (_66562 : type418 A) (y : type417 A) (lt2 : type1402 A) : (term409 A _66562 y lt2) = (term411 A _66562 y lt2).
Proof. exact (TRANS (@lem5107396 A _66562 y lt2) (@lem5107397 A _66562 y lt2)). Qed.
Lemma lem5107399 {A : Type'} (_66562 : type418 A) (y : type417 A) : (term412 A _66562 y) = (term413 A _66562 y).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5107398 A _66562 y lt2)). Qed.
Lemma lem5107400 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5107401 {A : Type'} (_66562 : type418 A) (y : type417 A) : (term414 A _66562 y) = (term415 A _66562 y).
Proof. exact (MK_COMB (@lem5107400 A) (@lem5107399 A _66562 y)). Qed.
Lemma lem5107402 {A : Type'} (_66562 : type418 A) : (term416 A _66562) = (term417 A _66562).
Proof. exact (fun_ext (fun y : type417 A => @lem5107401 A _66562 y)). Qed.
Lemma lem5107403 {A : Type'} : (@ex ((A -> A -> Prop) -> A -> A -> A)) = (@ex ((A -> A -> Prop) -> A -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> A -> A -> A))). Qed.
Lemma lem5107404 {A : Type'} (_66562 : type418 A) : (term399 A _66562) = (term418 A _66562).
Proof. exact (MK_COMB (@lem5107403 A) (@lem5107402 A _66562)). Qed.
Lemma lem5107405 {A : Type'} (_66562 : type418 A) : ((term398 A _66562) = (term399 A _66562)) = ((term395 A _66562) = (term418 A _66562)).
Proof. exact (MK_COMB (@lem5107393 A _66562) (@lem5107404 A _66562)). Qed.
Lemma lem5107406 {A : Type'} (_66562 : type418 A) : (term395 A _66562) = (term418 A _66562).
Proof. exact (EQ_MP (@lem5107405 A _66562) (@lem5107380 A _66562)). Qed.
Lemma lem5107407 {A : Type'} (_66562 : type418 A) : (term326 A _66562) = (term418 A _66562).
Proof. exact (TRANS (@lem5107376 A _66562) (@lem5107406 A _66562)). Qed.
Lemma lem5107408 {A : Type'} (_66562 : type418 A) : (term323 A _66562) = (term323 A _66562).
Proof. exact (eq_refl (term323 A _66562)). Qed.
Lemma lem5107409 {A : Type'} (_66562 : type418 A) : (term327 A _66562) = (term419 A _66562).
Proof. exact (MK_COMB (@lem5107408 A _66562) (@lem5107407 A _66562)). Qed.
Lemma lem5107411 {A : Type'} (P : Prop) (Q : A -> Prop) : (term420 A P Q) = (term421 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5107412 {A : Type'} (P : Prop) (Q : type83 A) : (term422 A P Q) = (term423 A P Q).
Proof. exact (@lem5107411 (type417 A) P Q). Qed.
Lemma lem5107413 {A : Type'} (_66562 : type418 A) : (term424 A _66562) = (term425 A _66562).
Proof. exact (@lem5107412 A (term321 A _66562) (term417 A _66562)). Qed.
Lemma lem5107414 {A : Type'} (_66562 : type418 A) (y : type417 A) : (term426 A _66562 y) = (term415 A _66562 y).
Proof. exact (eq_refl (term426 A _66562 y)). Qed.
Lemma lem5107415 {A : Type'} (_66562 : type418 A) : (term427 A _66562) = (term417 A _66562).
Proof. exact (fun_ext (fun y : type417 A => @lem5107414 A _66562 y)). Qed.
Lemma lem5107416 {A : Type'} : (@ex ((A -> A -> Prop) -> A -> A -> A)) = (@ex ((A -> A -> Prop) -> A -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> A -> A -> A))). Qed.
Lemma lem5107417 {A : Type'} (_66562 : type418 A) : (term428 A _66562) = (term418 A _66562).
Proof. exact (MK_COMB (@lem5107416 A) (@lem5107415 A _66562)). Qed.
Lemma lem5107418 {A : Type'} (_66562 : type418 A) : (term323 A _66562) = (term323 A _66562).
Proof. exact (eq_refl (term323 A _66562)). Qed.
Lemma lem5107419 {A : Type'} (_66562 : type418 A) : (term424 A _66562) = (term419 A _66562).
Proof. exact (MK_COMB (@lem5107418 A _66562) (@lem5107417 A _66562)). Qed.
Lemma lem5107420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5107421 {A : Type'} (_66562 : type418 A) : (term429 A _66562) = (term430 A _66562).
Proof. exact (MK_COMB (@lem5107420) (@lem5107419 A _66562)). Qed.
Lemma lem5107422 {A : Type'} (_66562 : type418 A) (y : type417 A) : (term426 A _66562 y) = (term415 A _66562 y).
Proof. exact (eq_refl (term426 A _66562 y)). Qed.
Lemma lem5107423 {A : Type'} (_66562 : type418 A) : (term323 A _66562) = (term323 A _66562).
Proof. exact (eq_refl (term323 A _66562)). Qed.
Lemma lem5107424 {A : Type'} (_66562 : type418 A) (y : type417 A) : (term431 A _66562 y) = (term432 A _66562 y).
Proof. exact (MK_COMB (@lem5107423 A _66562) (@lem5107422 A _66562 y)). Qed.
Lemma lem5107425 {A : Type'} (_66562 : type418 A) : (term433 A _66562) = (term434 A _66562).
Proof. exact (fun_ext (fun y : type417 A => @lem5107424 A _66562 y)). Qed.
Lemma lem5107426 {A : Type'} : (@ex ((A -> A -> Prop) -> A -> A -> A)) = (@ex ((A -> A -> Prop) -> A -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> A -> A -> A))). Qed.
Lemma lem5107427 {A : Type'} (_66562 : type418 A) : (term425 A _66562) = (term435 A _66562).
Proof. exact (MK_COMB (@lem5107426 A) (@lem5107425 A _66562)). Qed.
Lemma lem5107428 {A : Type'} (_66562 : type418 A) : ((term424 A _66562) = (term425 A _66562)) = ((term419 A _66562) = (term435 A _66562)).
Proof. exact (MK_COMB (@lem5107421 A _66562) (@lem5107427 A _66562)). Qed.
Lemma lem5107429 {A : Type'} (_66562 : type418 A) : (term419 A _66562) = (term435 A _66562).
Proof. exact (EQ_MP (@lem5107428 A _66562) (@lem5107413 A _66562)). Qed.
Lemma lem5107430 {A : Type'} (_66562 : type418 A) : (term327 A _66562) = (term435 A _66562).
Proof. exact (TRANS (@lem5107409 A _66562) (@lem5107429 A _66562)). Qed.
Lemma lem5107431 {A : Type'} (_66562 : type418 A) : (term259 A _66562) = (term435 A _66562).
Proof. exact (TRANS (@lem5107285 A _66562) (@lem5107430 A _66562)). Qed.
Lemma lem5107432 {A : Type'} (_66562 : type418 A) : (term228 A _66562) = (term435 A _66562).
Proof. exact (TRANS (@lem5106852 A _66562) (@lem5107431 A _66562)). Qed.
Lemma lem5107433 {A : Type'} (_66562 : type418 A) (h1 : term228 A _66562) : term435 A _66562.
Proof. exact (EQ_MP (@lem5107432 A _66562) (@lem5106808 A _66562 h1)). Qed.
Lemma lem5107434 {A : Type'} (lt2 : type1402 A) (x : A) : (term164 A lt2 x) = (term164 A lt2 x).
Proof. exact (eq_refl (term164 A lt2 x)). Qed.
Lemma lem5107435 {A : Type'} (lt2 : type1402 A) : (term165 A lt2) = (term165 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5107434 A lt2 x)). Qed.
Lemma lem5107436 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5107445 {A : Type'} (lt2 : type1402 A) : (term56 A lt2) = (term56 A lt2).
Proof. exact (MK_COMB (@lem5107436 A) (@lem5107435 A lt2)). Qed.
Lemma lem5107446 {A : Type'} (lt2 : type1402 A) (h1 : term56 A lt2) : term56 A lt2.
Proof. exact (EQ_MP (@lem5107445 A lt2) (@lem5106809 A lt2 h1)). Qed.
Lemma lem5107562 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term104 A lt2 n s m) = (term695 A lt2 n s m).
Proof. exact (@lem17265 (Peano.lt m n) (term69 A lt2 n s m)). Qed.
Lemma lem5107563 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term106 A lt2 s m) = (term696 A lt2 s m).
Proof. exact (fun_ext (fun n : nat => @lem5107562 A lt2 n s m)). Qed.
Lemma lem5107564 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5107565 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term108 A lt2 s m) = (term697 A lt2 s m).
Proof. exact (MK_COMB (@lem5107564) (@lem5107563 A lt2 s m)). Qed.
Lemma lem5107566 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term110 A lt2 s) = (term698 A lt2 s).
Proof. exact (fun_ext (fun m : nat => @lem5107565 A lt2 s m)). Qed.
Lemma lem5107567 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5107624 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term62 A lt2 s) = (term699 A lt2 s).
Proof. exact (MK_COMB (@lem5107567) (@lem5107566 A lt2 s)). Qed.
Lemma lem5107625 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term699 A lt2 s.
Proof. exact (EQ_MP (@lem5107624 A lt2 s) (@lem5106813 A lt2 s h1)). Qed.
Lemma lem5107632 {A : Type'} (s : nat -> A) (x : nat) (y : nat) : (term700 A s x y) = (term701 A s x y).
Proof. exact (@lem17362 ((s x) = (s y)) (x = y)). Qed.
Lemma lem5107633 (P : nat -> Prop) : (term451 P) = (term452 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5107634 {A : Type'} (s : nat -> A) (x : nat) : (term702 A s x) = (term703 A s x).
Proof. exact (@lem5107633 (term663 A s x)). Qed.
Lemma lem5107635 {A : Type'} (s : nat -> A) (x : nat) (y : nat) : (term704 A s x y) = (term662 A s x y).
Proof. exact (eq_refl (term704 A s x y)). Qed.
Lemma lem5107636 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5107637 {A : Type'} (s : nat -> A) (x : nat) (y : nat) : (term705 A s x y) = (term700 A s x y).
Proof. exact (MK_COMB (@lem5107636) (@lem5107635 A s x y)). Qed.
Lemma lem5107638 {A : Type'} (s : nat -> A) (x : nat) (y : nat) : (term705 A s x y) = (term701 A s x y).
Proof. exact (TRANS (@lem5107637 A s x y) (@lem5107632 A s x y)). Qed.
Lemma lem5107639 {A : Type'} (s : nat -> A) (x : nat) : (term706 A s x) = (term707 A s x).
Proof. exact (fun_ext (fun y : nat => @lem5107638 A s x y)). Qed.
Lemma lem5107640 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5107641 {A : Type'} (s : nat -> A) (x : nat) : (term703 A s x) = (term708 A s x).
Proof. exact (MK_COMB (@lem5107640) (@lem5107639 A s x)). Qed.
Lemma lem5107642 {A : Type'} (s : nat -> A) (x : nat) : (term702 A s x) = (term708 A s x).
Proof. exact (TRANS (@lem5107634 A s x) (@lem5107641 A s x)). Qed.
Lemma lem5107643 (P : nat -> Prop) : (term451 P) = (term452 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem5107644 {A : Type'} (s : nat -> A) : (term629 A s) = (term709 A s).
Proof. exact (@lem5107643 (term665 A s)). Qed.
Lemma lem5107645 {A : Type'} (s : nat -> A) (x : nat) : (term710 A s x) = (term664 A s x).
Proof. exact (eq_refl (term710 A s x)). Qed.
Lemma lem5107646 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5107647 {A : Type'} (s : nat -> A) (x : nat) : (term711 A s x) = (term702 A s x).
Proof. exact (MK_COMB (@lem5107646) (@lem5107645 A s x)). Qed.
Lemma lem5107648 {A : Type'} (s : nat -> A) (x : nat) : (term711 A s x) = (term708 A s x).
Proof. exact (TRANS (@lem5107647 A s x) (@lem5107642 A s x)). Qed.
Lemma lem5107649 {A : Type'} (s : nat -> A) : (term712 A s) = (term713 A s).
Proof. exact (fun_ext (fun x : nat => @lem5107648 A s x)). Qed.
Lemma lem5107650 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem5107651 {A : Type'} (s : nat -> A) : (term709 A s) = (term714 A s).
Proof. exact (MK_COMB (@lem5107650) (@lem5107649 A s)). Qed.
Lemma lem5107708 {A : Type'} (s : nat -> A) : (term629 A s) = (term714 A s).
Proof. exact (TRANS (@lem5107644 A s) (@lem5107651 A s)). Qed.
Lemma lem5107709 {A : Type'} (s : nat -> A) (h1 : term629 A s) : term714 A s.
Proof. exact (EQ_MP (@lem5107708 A s) (@lem5106814 A s h1)). Qed.
Lemma lem5107718 (m : nat) (n : nat) : (term658 m n) = (term658 m n).
Proof. exact (eq_refl (term658 m n)). Qed.
Lemma lem5107719 (m : nat) : (term659 m) = (term659 m).
Proof. exact (fun_ext (fun n : nat => @lem5107718 m n)). Qed.
Lemma lem5107720 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5107721 (m : nat) : (term660 m) = (term660 m).
Proof. exact (MK_COMB (@lem5107720) (@lem5107719 m)). Qed.
Lemma lem5107722 : term661 = term661.
Proof. exact (fun_ext (fun m : nat => @lem5107721 m)). Qed.
Lemma lem5107723 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5107780 : term636 = term636.
Proof. exact (MK_COMB (@lem5107723) (@lem5107722)). Qed.
Lemma lem5107781 (h1 : term636) : term636.
Proof. exact (EQ_MP (@lem5107780) (@lem5106815 h1)). Qed.
Lemma lem5107782 {A : Type'} (s : nat -> A) (x : nat) (h1 : term708 A s x) : term708 A s x.
Proof. exact (h1). Qed.
Lemma lem5107783 {A : Type'} (s : nat -> A) (x : nat) (y : nat) (h1 : term701 A s x y) : term701 A s x y.
Proof. exact (h1). Qed.
Lemma lem5107785 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5107792 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5107793 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5107792 A (A -> Prop) f x). Qed.
Lemma lem5107794 {A : Type'} (lt2 : type1402 A) (x : A) : (lt2 x) = (@I (A -> A -> Prop) lt2 x).
Proof. exact (@lem5107793 A lt2 x). Qed.
Lemma lem5107795 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5107796 {A : Type'} (lt2 : type1402 A) (x : A) : (lt2 x x) = (@I (A -> A -> Prop) lt2 x x).
Proof. exact (MK_COMB (@lem5107794 A lt2 x) (@lem5107795 A x)). Qed.
Lemma lem5107798 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5107799 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5107798 A Prop f x). Qed.
Lemma lem5107800 {A : Type'} (lt2 : type1402 A) (x : A) : (@I (A -> A -> Prop) lt2 x x) = (term715 A lt2 x).
Proof. exact (@lem5107799 A (@I (A -> A -> Prop) lt2 x) x). Qed.
Lemma lem5107802 {A : Type'} (lt2 : type1402 A) (x : A) : (lt2 x x) = (term715 A lt2 x).
Proof. exact (TRANS (@lem5107796 A lt2 x) (@lem5107800 A lt2 x)). Qed.
Lemma lem5107803 {A : Type'} (lt2 : type1402 A) (x : A) : (term164 A lt2 x) = (term716 A lt2 x).
Proof. exact (MK_COMB (@lem5107785) (@lem5107802 A lt2 x)). Qed.
Lemma lem5107804 {A : Type'} (lt2 : type1402 A) : (term165 A lt2) = (term717 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5107803 A lt2 x)). Qed.
Lemma lem5107805 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5107806 {A : Type'} (lt2 : type1402 A) : (term56 A lt2) = (term718 A lt2).
Proof. exact (MK_COMB (@lem5107805 A) (@lem5107804 A lt2)). Qed.
Lemma lem5107807 {A : Type'} (lt2 : type1402 A) (h1 : term56 A lt2) : term718 A lt2.
Proof. exact (EQ_MP (@lem5107806 A lt2) (@lem5107446 A lt2 h1)). Qed.
Lemma lem5107956 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem5107961 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5107962 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5107961 nat A f x). Qed.
Lemma lem5107964 {A : Type'} (s : nat -> A) (n : nat) : (s n) = (@I (nat -> A) s n).
Proof. exact (@lem5107962 A s n). Qed.
Lemma lem5107969 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5107970 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5107969 nat A f x). Qed.
Lemma lem5107972 {A : Type'} (s : nat -> A) (m : nat) : (s m) = (@I (nat -> A) s m).
Proof. exact (@lem5107970 A s m). Qed.
Lemma lem5107973 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term575 A lt2 s n) = (term576 A lt2 s n).
Proof. exact (MK_COMB (@lem5107956 A lt2) (@lem5107964 A s n)). Qed.
Lemma lem5107974 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term69 A lt2 n s m) = (term577 A lt2 n s m).
Proof. exact (MK_COMB (@lem5107973 A lt2 s n) (@lem5107972 A s m)). Qed.
Lemma lem5107976 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5107977 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5107976 A (A -> Prop) f x). Qed.
Lemma lem5107978 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term576 A lt2 s n) = (term578 A lt2 s n).
Proof. exact (@lem5107977 A lt2 (@I (nat -> A) s n)). Qed.
Lemma lem5107979 {A : Type'} (s : nat -> A) (m : nat) : (@I (nat -> A) s m) = (@I (nat -> A) s m).
Proof. exact (eq_refl (@I (nat -> A) s m)). Qed.
Lemma lem5107980 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term577 A lt2 n s m) = (term579 A lt2 n s m).
Proof. exact (MK_COMB (@lem5107978 A lt2 s n) (@lem5107979 A s m)). Qed.
Lemma lem5107982 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5107983 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5107982 A Prop f x). Qed.
Lemma lem5107984 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term579 A lt2 n s m) = (term580 A lt2 n s m).
Proof. exact (@lem5107983 A (term578 A lt2 s n) (@I (nat -> A) s m)). Qed.
Lemma lem5107985 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term577 A lt2 n s m) = (term580 A lt2 n s m).
Proof. exact (TRANS (@lem5107980 A lt2 n s m) (@lem5107984 A lt2 n s m)). Qed.
Lemma lem5107986 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term69 A lt2 n s m) = (term580 A lt2 n s m).
Proof. exact (TRANS (@lem5107974 A lt2 n s m) (@lem5107985 A lt2 n s m)). Qed.
Lemma lem5107987 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5107994 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5107995 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem5107994 nat (nat -> Prop) f x). Qed.
Lemma lem5107996 (m : nat) : (Peano.lt m) = (@I (nat -> nat -> Prop) Peano.lt m).
Proof. exact (@lem5107995 Peano.lt m). Qed.
Lemma lem5107997 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem5107998 (m : nat) (n : nat) : (Peano.lt m n) = (@I (nat -> nat -> Prop) Peano.lt m n).
Proof. exact (MK_COMB (@lem5107996 m) (@lem5107997 n)). Qed.
Lemma lem5108000 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5108001 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem5108000 nat Prop f x). Qed.
Lemma lem5108002 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.lt m n) = (term719 m n).
Proof. exact (@lem5108001 (@I (nat -> nat -> Prop) Peano.lt m) n). Qed.
Lemma lem5108004 (m : nat) (n : nat) : (Peano.lt m n) = (term719 m n).
Proof. exact (TRANS (@lem5107998 m n) (@lem5108002 m n)). Qed.
Lemma lem5108005 (m : nat) (n : nat) : (term720 m n) = (term721 m n).
Proof. exact (MK_COMB (@lem5107987) (@lem5108004 m n)). Qed.
Lemma lem5108006 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5108007 (m : nat) (n : nat) : (term722 m n) = (term723 m n).
Proof. exact (MK_COMB (@lem5108006) (@lem5108005 m n)). Qed.
Lemma lem5108008 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term695 A lt2 n s m) = (term724 A lt2 n s m).
Proof. exact (MK_COMB (@lem5108007 m n) (@lem5107986 A lt2 n s m)). Qed.
Lemma lem5108009 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term696 A lt2 s m) = (term725 A lt2 s m).
Proof. exact (fun_ext (fun n : nat => @lem5108008 A lt2 n s m)). Qed.
Lemma lem5108010 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5108011 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term697 A lt2 s m) = (term726 A lt2 s m).
Proof. exact (MK_COMB (@lem5108010) (@lem5108009 A lt2 s m)). Qed.
Lemma lem5108012 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term698 A lt2 s) = (term727 A lt2 s).
Proof. exact (fun_ext (fun m : nat => @lem5108011 A lt2 s m)). Qed.
Lemma lem5108013 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5108014 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term699 A lt2 s) = (term728 A lt2 s).
Proof. exact (MK_COMB (@lem5108013) (@lem5108012 A lt2 s)). Qed.
Lemma lem5108015 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term728 A lt2 s.
Proof. exact (EQ_MP (@lem5108014 A lt2 s) (@lem5107625 A lt2 s h1)). Qed.
Lemma lem5108020 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem5108027 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5108028 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem5108027 nat (nat -> Prop) f x). Qed.
Lemma lem5108029 (n : nat) : (Peano.lt n) = (@I (nat -> nat -> Prop) Peano.lt n).
Proof. exact (@lem5108028 Peano.lt n). Qed.
Lemma lem5108030 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem5108031 (n : nat) (m : nat) : (Peano.lt n m) = (@I (nat -> nat -> Prop) Peano.lt n m).
Proof. exact (MK_COMB (@lem5108029 n) (@lem5108030 m)). Qed.
Lemma lem5108033 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5108034 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem5108033 nat Prop f x). Qed.
Lemma lem5108035 (n : nat) (m : nat) : (@I (nat -> nat -> Prop) Peano.lt n m) = (term719 n m).
Proof. exact (@lem5108034 (@I (nat -> nat -> Prop) Peano.lt n) m). Qed.
Lemma lem5108037 (n : nat) (m : nat) : (Peano.lt n m) = (term719 n m).
Proof. exact (TRANS (@lem5108031 n m) (@lem5108035 n m)). Qed.
Lemma lem5108038 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5108039 (n : nat) (m : nat) : (term729 n m) = (term730 n m).
Proof. exact (MK_COMB (@lem5108038) (@lem5108037 n m)). Qed.
Lemma lem5108040 (m : nat) (n : nat) : (term731 m n) = (term732 m n).
Proof. exact (MK_COMB (@lem5108039 n m) (@lem5108020 m n)). Qed.
Lemma lem5108047 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5108048 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem5108047 nat (nat -> Prop) f x). Qed.
Lemma lem5108049 (m : nat) : (Peano.lt m) = (@I (nat -> nat -> Prop) Peano.lt m).
Proof. exact (@lem5108048 Peano.lt m). Qed.
Lemma lem5108050 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem5108051 (m : nat) (n : nat) : (Peano.lt m n) = (@I (nat -> nat -> Prop) Peano.lt m n).
Proof. exact (MK_COMB (@lem5108049 m) (@lem5108050 n)). Qed.
Lemma lem5108053 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5108054 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem5108053 nat Prop f x). Qed.
Lemma lem5108055 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.lt m n) = (term719 m n).
Proof. exact (@lem5108054 (@I (nat -> nat -> Prop) Peano.lt m) n). Qed.
Lemma lem5108057 (m : nat) (n : nat) : (Peano.lt m n) = (term719 m n).
Proof. exact (TRANS (@lem5108051 m n) (@lem5108055 m n)). Qed.
Lemma lem5108058 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5108059 (m : nat) (n : nat) : (term729 m n) = (term730 m n).
Proof. exact (MK_COMB (@lem5108058) (@lem5108057 m n)). Qed.
Lemma lem5108060 (m : nat) (n : nat) : (term658 m n) = (term733 m n).
Proof. exact (MK_COMB (@lem5108059 m n) (@lem5108040 m n)). Qed.
Lemma lem5108061 (m : nat) : (term659 m) = (term734 m).
Proof. exact (fun_ext (fun n : nat => @lem5108060 m n)). Qed.
Lemma lem5108062 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5108063 (m : nat) : (term660 m) = (term735 m).
Proof. exact (MK_COMB (@lem5108062) (@lem5108061 m)). Qed.
Lemma lem5108064 : term661 = term736.
Proof. exact (fun_ext (fun m : nat => @lem5108063 m)). Qed.
Lemma lem5108065 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5108066 : term636 = term737.
Proof. exact (MK_COMB (@lem5108065) (@lem5108064)). Qed.
Lemma lem5108067 (h1 : term636) : term737.
Proof. exact (EQ_MP (@lem5108066) (@lem5107781 h1)). Qed.
Lemma lem5108074 (x : nat) (y : nat) : (term738 x y) = (term738 x y).
Proof. exact (eq_refl (term738 x y)). Qed.
Lemma lem5108075 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5108080 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5108081 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5108080 nat A f x). Qed.
Lemma lem5108083 {A : Type'} (s : nat -> A) (x : nat) : (s x) = (@I (nat -> A) s x).
Proof. exact (@lem5108081 A s x). Qed.
Lemma lem5108088 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5108089 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5108088 nat A f x). Qed.
Lemma lem5108091 {A : Type'} (s : nat -> A) (y : nat) : (s y) = (@I (nat -> A) s y).
Proof. exact (@lem5108089 A s y). Qed.
Lemma lem5108092 {A : Type'} (s : nat -> A) (x : nat) : (term739 A s x) = (term740 A s x).
Proof. exact (MK_COMB (@lem5108075 A) (@lem5108083 A s x)). Qed.
Lemma lem5108093 {A : Type'} (x : nat) (s : nat -> A) (y : nat) : ((s x) = (s y)) = ((@I (nat -> A) s x) = (@I (nat -> A) s y)).
Proof. exact (MK_COMB (@lem5108092 A s x) (@lem5108091 A s y)). Qed.
Lemma lem5108094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5108095 {A : Type'} (x : nat) (s : nat -> A) (y : nat) : (term741 A x s y) = (term742 A x s y).
Proof. exact (MK_COMB (@lem5108094) (@lem5108093 A x s y)). Qed.
Lemma lem5108096 {A : Type'} (s : nat -> A) (x : nat) (y : nat) : (term701 A s x y) = (term743 A s x y).
Proof. exact (MK_COMB (@lem5108095 A x s y) (@lem5108074 x y)). Qed.
Lemma lem5108097 {A : Type'} (s : nat -> A) (x : nat) (y : nat) (h1 : term701 A s x y) : term743 A s x y.
Proof. exact (EQ_MP (@lem5108096 A s x y) (@lem5107783 A s x y h1)). Qed.
Lemma lem5108324 {A : Type'} (lt2 : type1402 A) (x : A) : (term716 A lt2 x) = (term716 A lt2 x).
Proof. exact (eq_refl (term716 A lt2 x)). Qed.
Lemma lem5108325 {A : Type'} (lt2 : type1402 A) : (term717 A lt2) = (term717 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5108324 A lt2 x)). Qed.
Lemma lem5108326 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5108328 {A : Type'} (lt2 : type1402 A) : (term718 A lt2) = (term718 A lt2).
Proof. exact (MK_COMB (@lem5108326 A) (@lem5108325 A lt2)). Qed.
Lemma lem5108329 {A : Type'} (lt2 : type1402 A) (h1 : term56 A lt2) : term718 A lt2.
Proof. exact (EQ_MP (@lem5108328 A lt2) (@lem5107807 A lt2 h1)). Qed.
Lemma lem5108376 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term724 A lt2 n s m) = (term724 A lt2 n s m).
Proof. exact (eq_refl (term724 A lt2 n s m)). Qed.
Lemma lem5108377 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term725 A lt2 s m) = (term725 A lt2 s m).
Proof. exact (fun_ext (fun n : nat => @lem5108376 A lt2 n s m)). Qed.
Lemma lem5108378 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5108379 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term726 A lt2 s m) = (term726 A lt2 s m).
Proof. exact (MK_COMB (@lem5108378) (@lem5108377 A lt2 s m)). Qed.
Lemma lem5108380 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term727 A lt2 s) = (term727 A lt2 s).
Proof. exact (fun_ext (fun m : nat => @lem5108379 A lt2 s m)). Qed.
Lemma lem5108381 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5108383 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term728 A lt2 s) = (term728 A lt2 s).
Proof. exact (MK_COMB (@lem5108381) (@lem5108380 A lt2 s)). Qed.
Lemma lem5108384 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term728 A lt2 s.
Proof. exact (EQ_MP (@lem5108383 A lt2 s) (@lem5108015 A lt2 s h1)). Qed.
Lemma lem5108398 (m : nat) (n : nat) : (term733 m n) = (term733 m n).
Proof. exact (eq_refl (term733 m n)). Qed.
Lemma lem5108399 (m : nat) : (term734 m) = (term734 m).
Proof. exact (fun_ext (fun n : nat => @lem5108398 m n)). Qed.
Lemma lem5108400 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5108401 (m : nat) : (term735 m) = (term735 m).
Proof. exact (MK_COMB (@lem5108400) (@lem5108399 m)). Qed.
Lemma lem5108402 : term736 = term736.
Proof. exact (fun_ext (fun m : nat => @lem5108401 m)). Qed.
Lemma lem5108403 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5108405 : term737 = term737.
Proof. exact (MK_COMB (@lem5108403) (@lem5108402)). Qed.
Lemma lem5108406 (h1 : term636) : term737.
Proof. exact (EQ_MP (@lem5108405) (@lem5108067 h1)). Qed.
Lemma lem5108484 {A : Type'} (_66563 : A) (lt2 : type1402 A) (h1 : term56 A lt2) : term744 A lt2 _66563.
Proof. exact (@lem5108329 A lt2 h1 _66563). Qed.
Lemma lem5108485 {A : Type'} (lt2 : type1402 A) (_66563 : A) : (term744 A lt2 _66563) = (term716 A lt2 _66563).
Proof. exact (eq_refl (term744 A lt2 _66563)). Qed.
Lemma lem5108502 {A : Type'} (_66569 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term745 A lt2 s _66569.
Proof. exact (@lem5108384 A lt2 s h1 _66569). Qed.
Lemma lem5108503 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66569 : nat) : (term745 A lt2 s _66569) = (term726 A lt2 s _66569).
Proof. exact (eq_refl (term745 A lt2 s _66569)). Qed.
Lemma lem5108504 {A : Type'} (_66569 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term726 A lt2 s _66569.
Proof. exact (EQ_MP (@lem5108503 A lt2 s _66569) (@lem5108502 A _66569 lt2 s h1)). Qed.
Lemma lem5108505 {A : Type'} (_66569 : nat) (_66570 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term746 A lt2 s _66569 _66570.
Proof. exact (@lem5108504 A _66569 lt2 s h1 _66570). Qed.
Lemma lem5108506 {A : Type'} (lt2 : type1402 A) (_66570 : nat) (s : nat -> A) (_66569 : nat) : (term746 A lt2 s _66569 _66570) = (term724 A lt2 _66570 s _66569).
Proof. exact (eq_refl (term746 A lt2 s _66569 _66570)). Qed.
Lemma lem5108508 (_66571 : nat) (h1 : term636) : term747 _66571.
Proof. exact (@lem5108406 h1 _66571). Qed.
Lemma lem5108509 (_66571 : nat) : (term747 _66571) = (term735 _66571).
Proof. exact (eq_refl (term747 _66571)). Qed.
Lemma lem5108510 (_66571 : nat) (h1 : term636) : term735 _66571.
Proof. exact (EQ_MP (@lem5108509 _66571) (@lem5108508 _66571 h1)). Qed.
Lemma lem5108511 (_66571 : nat) (_66572 : nat) (h1 : term636) : term748 _66571 _66572.
Proof. exact (@lem5108510 _66571 h1 _66572). Qed.
Lemma lem5108512 (_66571 : nat) (_66572 : nat) : (term748 _66571 _66572) = (term733 _66571 _66572).
Proof. exact (eq_refl (term748 _66571 _66572)). Qed.
Lemma lem5108536 {A : Type'} (_66563 : A) (lt2 : type1402 A) (h1 : term56 A lt2) : term716 A lt2 _66563.
Proof. exact (EQ_MP (@lem5108485 A lt2 _66563) (@lem5108484 A _66563 lt2 h1)). Qed.
Lemma lem5108558 {A : Type'} (_66570 : nat) (_66569 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term724 A lt2 _66570 s _66569.
Proof. exact (EQ_MP (@lem5108506 A lt2 _66570 s _66569) (@lem5108505 A _66569 _66570 lt2 s h1)). Qed.
Lemma lem5108568 (_66571 : nat) (_66572 : nat) (h1 : term636) : term733 _66571 _66572.
Proof. exact (EQ_MP (@lem5108512 _66571 _66572) (@lem5108511 _66571 _66572 h1)). Qed.
Lemma lem5108623 {A : Type'} : (@I (A -> Prop)) = (@I (A -> Prop)).
Proof. exact (eq_refl (@I (A -> Prop))). Qed.
Lemma lem5108624 {A : Type'} (_66588 : A -> Prop) (_66590 : A -> Prop) (h1 : _66588 = _66590) : _66588 = _66590.
Proof. exact (h1). Qed.
Lemma lem5108625 {A : Type'} (_66589 : A) (_66591 : A) (h1 : _66589 = _66591) : _66589 = _66591.
Proof. exact (h1). Qed.
Lemma lem5108626 {A : Type'} (_66588 : A -> Prop) (_66590 : A -> Prop) (h1 : _66588 = _66590) : (@I (A -> Prop) _66588) = (@I (A -> Prop) _66590).
Proof. exact (MK_COMB (@lem5108623 A) (@lem5108624 A _66588 _66590 h1)). Qed.
Lemma lem5108627 {A : Type'} (_66589 : A) (_66591 : A) (_66588 : A -> Prop) (_66590 : A -> Prop) (h1 : _66589 = _66591) (h2 : _66588 = _66590) : (@I (A -> Prop) _66588 _66589) = (@I (A -> Prop) _66590 _66591).
Proof. exact (MK_COMB (@lem5108626 A _66588 _66590 h2) (@lem5108625 A _66589 _66591 h1)). Qed.
Lemma lem5108629 (b : Prop) (a : Prop) : term749 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5108630 {A : Type'} (_66590 : A -> Prop) (_66591 : A) (_66588 : A -> Prop) (_66589 : A) : term750 A _66590 _66591 _66588 _66589.
Proof. exact (@lem5108629 (@I (A -> Prop) _66590 _66591) (@I (A -> Prop) _66588 _66589)). Qed.
Lemma lem5108631 {A : Type'} (_66589 : A) (_66591 : A) (_66588 : A -> Prop) (_66590 : A -> Prop) (h1 : _66589 = _66591) (h2 : _66588 = _66590) : term751 A _66590 _66591 _66588 _66589.
Proof. exact (@lem5108630 A _66590 _66591 _66588 _66589 (@lem5108627 A _66589 _66591 _66588 _66590 h1 h2)). Qed.
Lemma lem5108632 {A : Type'} (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) (_66591 : A) (h1 : _66589 = _66591) : term752 A _66590 _66591 _66588 _66589.
Proof. exact (fun h0 : _66588 = _66590 => @lem5108631 A _66589 _66591 _66588 _66590 h1 h0). Qed.
Lemma lem5108634 (a : Prop) (b : Prop) : (a -> b) = (term753 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5108635 {A : Type'} (_66590 : A -> Prop) (_66591 : A) (_66588 : A -> Prop) (_66589 : A) : (term752 A _66590 _66591 _66588 _66589) = (term754 A _66590 _66591 _66588 _66589).
Proof. exact (@lem5108634 (_66588 = _66590) (term751 A _66590 _66591 _66588 _66589)). Qed.
Lemma lem5108636 {A : Type'} (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) (_66591 : A) (h1 : _66589 = _66591) : term754 A _66590 _66591 _66588 _66589.
Proof. exact (EQ_MP (@lem5108635 A _66590 _66591 _66588 _66589) (@lem5108632 A _66590 _66588 _66589 _66591 h1)). Qed.
Lemma lem5108637 {A : Type'} (_66590 : A -> Prop) (_66591 : A) (_66588 : A -> Prop) (_66589 : A) : term755 A _66590 _66591 _66588 _66589.
Proof. exact (fun h0 : _66589 = _66591 => @lem5108636 A _66590 _66588 _66589 _66591 h0). Qed.
Lemma lem5108639 (a : Prop) (b : Prop) : (a -> b) = (term753 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5108640 {A : Type'} (_66590 : A -> Prop) (_66591 : A) (_66588 : A -> Prop) (_66589 : A) : (term755 A _66590 _66591 _66588 _66589) = (term756 A _66590 _66591 _66588 _66589).
Proof. exact (@lem5108639 (_66589 = _66591) (term754 A _66590 _66591 _66588 _66589)). Qed.
Lemma lem5108641 {A : Type'} (_66590 : A -> Prop) (_66591 : A) (_66588 : A -> Prop) (_66589 : A) : term756 A _66590 _66591 _66588 _66589.
Proof. exact (EQ_MP (@lem5108640 A _66590 _66591 _66588 _66589) (@lem5108637 A _66590 _66591 _66588 _66589)). Qed.
Lemma lem5108807 {A : Type'} : (@I (A -> A -> Prop)) = (@I (A -> A -> Prop)).
Proof. exact (eq_refl (@I (A -> A -> Prop))). Qed.
Lemma lem5108808 {A : Type'} (_66636 : type1402 A) (_66638 : type1402 A) (h1 : _66636 = _66638) : _66636 = _66638.
Proof. exact (h1). Qed.
Lemma lem5108809 {A : Type'} (_66637 : A) (_66639 : A) (h1 : _66637 = _66639) : _66637 = _66639.
Proof. exact (h1). Qed.
Lemma lem5108810 {A : Type'} (_66636 : type1402 A) (_66638 : type1402 A) (h1 : _66636 = _66638) : (@I (A -> A -> Prop) _66636) = (@I (A -> A -> Prop) _66638).
Proof. exact (MK_COMB (@lem5108807 A) (@lem5108808 A _66636 _66638 h1)). Qed.
Lemma lem5108811 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) (h1 : _66637 = _66639) (h2 : _66636 = _66638) : (@I (A -> A -> Prop) _66636 _66637) = (@I (A -> A -> Prop) _66638 _66639).
Proof. exact (MK_COMB (@lem5108810 A _66636 _66638 h2) (@lem5108809 A _66637 _66639 h1)). Qed.
Lemma lem5108812 {A : Type'} (_66636 : type1402 A) (_66638 : type1402 A) (_66637 : A) (_66639 : A) (h1 : _66637 = _66639) : term757 A _66636 _66637 _66638 _66639.
Proof. exact (fun h0 : _66636 = _66638 => @lem5108811 A _66637 _66639 _66636 _66638 h1 h0). Qed.
Lemma lem5108814 (a : Prop) (b : Prop) : (a -> b) = (term753 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5108815 {A : Type'} (_66636 : type1402 A) (_66637 : A) (_66638 : type1402 A) (_66639 : A) : (term757 A _66636 _66637 _66638 _66639) = (term758 A _66636 _66637 _66638 _66639).
Proof. exact (@lem5108814 (_66636 = _66638) ((@I (A -> A -> Prop) _66636 _66637) = (@I (A -> A -> Prop) _66638 _66639))). Qed.
Lemma lem5108816 {A : Type'} (_66636 : type1402 A) (_66638 : type1402 A) (_66637 : A) (_66639 : A) (h1 : _66637 = _66639) : term758 A _66636 _66637 _66638 _66639.
Proof. exact (EQ_MP (@lem5108815 A _66636 _66637 _66638 _66639) (@lem5108812 A _66636 _66638 _66637 _66639 h1)). Qed.
Lemma lem5108817 {A : Type'} (_66636 : type1402 A) (_66637 : A) (_66638 : type1402 A) (_66639 : A) : term759 A _66636 _66637 _66638 _66639.
Proof. exact (fun h0 : _66637 = _66639 => @lem5108816 A _66636 _66638 _66637 _66639 h0). Qed.
Lemma lem5108819 (a : Prop) (b : Prop) : (a -> b) = (term753 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5108820 {A : Type'} (_66636 : type1402 A) (_66637 : A) (_66638 : type1402 A) (_66639 : A) : (term759 A _66636 _66637 _66638 _66639) = (term760 A _66636 _66637 _66638 _66639).
Proof. exact (@lem5108819 (_66637 = _66639) (term758 A _66636 _66637 _66638 _66639)). Qed.
Lemma lem5108821 {A : Type'} (_66636 : type1402 A) (_66637 : A) (_66638 : type1402 A) (_66639 : A) : term760 A _66636 _66637 _66638 _66639.
Proof. exact (EQ_MP (@lem5108820 A _66636 _66637 _66638 _66639) (@lem5108817 A _66636 _66637 _66638 _66639)). Qed.
Lemma lem5108855 {A : Type'} (s : nat -> A) (x : nat) (y : nat) (h1 : term701 A s x y) : (@I (nat -> A) s x) = (@I (nat -> A) s y).
Proof. exact (proj1 (@lem5108097 A s x y h1)). Qed.
Lemma lem5108856 {A : Type'} (s : nat -> A) (x : nat) (y : nat) (h1 : term701 A s x y) : term761 A x s y.
Proof. exact (fun h0 : term762 A x s y => @lem5108855 A s x y h1). Qed.
Lemma lem5108858 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5108859 {A : Type'} (x : nat) (s : nat -> A) (y : nat) : (term761 A x s y) = ((@I (nat -> A) s x) = (@I (nat -> A) s y)).
Proof. exact (@lem5108858 ((@I (nat -> A) s x) = (@I (nat -> A) s y))). Qed.
Lemma lem5108860 {A : Type'} (s : nat -> A) (x : nat) (y : nat) (h1 : term701 A s x y) : (@I (nat -> A) s x) = (@I (nat -> A) s y).
Proof. exact (EQ_MP (@lem5108859 A x s y) (@lem5108856 A s x y h1)). Qed.
Lemma lem5108862 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem5108863 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem5108862 A x). Qed.
Lemma lem5108864 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (y : nat) : (term578 A lt2 s y) = (term578 A lt2 s y).
Proof. exact (@lem5108863 A (term578 A lt2 s y)). Qed.
Lemma lem5108865 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (y : nat) : term763 A lt2 s y.
Proof. exact (fun h0 : term764 A lt2 s y => @lem5108864 A lt2 s y). Qed.
Lemma lem5108867 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5108868 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (y : nat) : (term763 A lt2 s y) = ((term578 A lt2 s y) = (term578 A lt2 s y)).
Proof. exact (@lem5108867 ((term578 A lt2 s y) = (term578 A lt2 s y))). Qed.
Lemma lem5108869 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (y : nat) : (term578 A lt2 s y) = (term578 A lt2 s y).
Proof. exact (EQ_MP (@lem5108868 A lt2 s y) (@lem5108865 A lt2 s y)). Qed.
Lemma lem5108871 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5108872 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5108871 A x). Qed.
Lemma lem5108873 {A : Type'} (s : nat -> A) (y : nat) : (@I (nat -> A) s y) = (@I (nat -> A) s y).
Proof. exact (@lem5108872 A (@I (nat -> A) s y)). Qed.
Lemma lem5108874 {A : Type'} (s : nat -> A) (y : nat) : term765 A s y.
Proof. exact (fun h0 : term766 A s y => @lem5108873 A s y). Qed.
Lemma lem5108876 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5108877 {A : Type'} (s : nat -> A) (y : nat) : (term765 A s y) = ((@I (nat -> A) s y) = (@I (nat -> A) s y)).
Proof. exact (@lem5108876 ((@I (nat -> A) s y) = (@I (nat -> A) s y))). Qed.
Lemma lem5108878 {A : Type'} (s : nat -> A) (y : nat) : (@I (nat -> A) s y) = (@I (nat -> A) s y).
Proof. exact (EQ_MP (@lem5108877 A s y) (@lem5108874 A s y)). Qed.
Lemma lem5108880 {A : Type'} (s : nat -> A) (x : nat) (y : nat) (h1 : term701 A s x y) : (@I (nat -> A) s x) = (@I (nat -> A) s y).
Proof. exact (proj1 (@lem5108097 A s x y h1)). Qed.
Lemma lem5108881 {A : Type'} (s : nat -> A) (x : nat) (y : nat) (h1 : term701 A s x y) : term761 A x s y.
Proof. exact (fun h0 : term762 A x s y => @lem5108880 A s x y h1). Qed.
Lemma lem5108883 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5108884 {A : Type'} (x : nat) (s : nat -> A) (y : nat) : (term761 A x s y) = ((@I (nat -> A) s x) = (@I (nat -> A) s y)).
Proof. exact (@lem5108883 ((@I (nat -> A) s x) = (@I (nat -> A) s y))). Qed.
Lemma lem5108885 {A : Type'} (s : nat -> A) (x : nat) (y : nat) (h1 : term701 A s x y) : (@I (nat -> A) s x) = (@I (nat -> A) s y).
Proof. exact (EQ_MP (@lem5108884 A x s y) (@lem5108881 A s x y h1)). Qed.
Lemma lem5108887 {A : Type'} (x : type1402 A) : x = x.
Proof. exact (@lem21386 (type1402 A) x). Qed.
Lemma lem5108888 {A : Type'} (x : type1402 A) : x = x.
Proof. exact (@lem5108887 A x). Qed.
Lemma lem5108889 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (@lem5108888 A lt2). Qed.
Lemma lem5108890 {A : Type'} (lt2 : type1402 A) : term767 A lt2.
Proof. exact (fun h0 : term768 A lt2 => @lem5108889 A lt2). Qed.
Lemma lem5108892 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5108893 {A : Type'} (lt2 : type1402 A) : (term767 A lt2) = (lt2 = lt2).
Proof. exact (@lem5108892 (lt2 = lt2)). Qed.
Lemma lem5108894 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (EQ_MP (@lem5108893 A lt2) (@lem5108890 A lt2)). Qed.
Lemma lem5108912 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5108913 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) : (term758 A _66636 _66637 _66638 _66639) = (term769 A _66637 _66639 _66636 _66638).
Proof. exact (@lem5108912 ((@I (A -> A -> Prop) _66636 _66637) = (@I (A -> A -> Prop) _66638 _66639)) (term770 A _66636 _66638)). Qed.
Lemma lem5108923 {A : Type'} (_66637 : A) (_66639 : A) : (term771 A _66637 _66639) = (term771 A _66637 _66639).
Proof. exact (eq_refl (term771 A _66637 _66639)). Qed.
Lemma lem5108924 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) : (term760 A _66636 _66637 _66638 _66639) = (term772 A _66637 _66639 _66636 _66638).
Proof. exact (MK_COMB (@lem5108923 A _66637 _66639) (@lem5108913 A _66637 _66639 _66636 _66638)). Qed.
Lemma lem5108928 (q : Prop) (p : Prop) (r : Prop) : (term45 p q r) = (term45 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5108929 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) : (term772 A _66637 _66639 _66636 _66638) = (term773 A _66637 _66639 _66636 _66638).
Proof. exact (@lem5108928 ((@I (A -> A -> Prop) _66636 _66637) = (@I (A -> A -> Prop) _66638 _66639)) (term774 A _66637 _66639) (term770 A _66636 _66638)). Qed.
Lemma lem5108951 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) : (term760 A _66636 _66637 _66638 _66639) = (term773 A _66637 _66639 _66636 _66638).
Proof. exact (TRANS (@lem5108924 A _66637 _66639 _66636 _66638) (@lem5108929 A _66637 _66639 _66636 _66638)). Qed.
Lemma lem5108952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5108953 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) : (term775 A _66636 _66637 _66638 _66639) = (term776 A _66637 _66639 _66636 _66638).
Proof. exact (MK_COMB (@lem5108952) (@lem5108951 A _66637 _66639 _66636 _66638)). Qed.
Lemma lem5108975 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) : (term773 A _66637 _66639 _66636 _66638) = (term773 A _66637 _66639 _66636 _66638).
Proof. exact (eq_refl (term773 A _66637 _66639 _66636 _66638)). Qed.
Lemma lem5108976 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) : ((term760 A _66636 _66637 _66638 _66639) = (term773 A _66637 _66639 _66636 _66638)) = ((term773 A _66637 _66639 _66636 _66638) = (term773 A _66637 _66639 _66636 _66638)).
Proof. exact (MK_COMB (@lem5108953 A _66637 _66639 _66636 _66638) (@lem5108975 A _66637 _66639 _66636 _66638)). Qed.
Lemma lem5108978 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5108979 (x : Prop) : (x = x) = True.
Proof. exact (@lem5108978 Prop x). Qed.
Lemma lem5108980 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) : ((term773 A _66637 _66639 _66636 _66638) = (term773 A _66637 _66639 _66636 _66638)) = True.
Proof. exact (@lem5108979 (term773 A _66637 _66639 _66636 _66638)). Qed.
Lemma lem5108981 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) : ((term760 A _66636 _66637 _66638 _66639) = (term773 A _66637 _66639 _66636 _66638)) = True.
Proof. exact (TRANS (@lem5108976 A _66637 _66639 _66636 _66638) (@lem5108980 A _66637 _66639 _66636 _66638)). Qed.
Lemma lem5108982 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) : True = ((term760 A _66636 _66637 _66638 _66639) = (term773 A _66637 _66639 _66636 _66638)).
Proof. exact (SYM (@lem5108981 A _66637 _66639 _66636 _66638)). Qed.
Lemma lem5108983 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) : (term760 A _66636 _66637 _66638 _66639) = (term773 A _66637 _66639 _66636 _66638).
Proof. exact (EQ_MP (@lem5108982 A _66637 _66639 _66636 _66638) (@lem0)). Qed.
Lemma lem5108984 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) : term773 A _66637 _66639 _66636 _66638.
Proof. exact (EQ_MP (@lem5108983 A _66637 _66639 _66636 _66638) (@lem5108821 A _66636 _66637 _66638 _66639)). Qed.
Lemma lem5108986 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5108987 {A : Type'} (_66636 : type1402 A) (_66637 : A) (_66638 : type1402 A) (_66639 : A) : (term773 A _66637 _66639 _66636 _66638) = (term777 A _66636 _66637 _66638 _66639).
Proof. exact (@lem5108986 (term778 A _66637 _66639 _66636 _66638) ((@I (A -> A -> Prop) _66636 _66637) = (@I (A -> A -> Prop) _66638 _66639))). Qed.
Lemma lem5108989 (a : Prop) (b : Prop) : (term605 a b) = (term606 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5108990 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) : (term779 A _66637 _66639 _66636 _66638) = (term780 A _66637 _66639 _66636 _66638).
Proof. exact (@lem5108989 (term774 A _66637 _66639) (term770 A _66636 _66638)). Qed.
Lemma lem5108992 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5108993 {A : Type'} (_66637 : A) (_66639 : A) : (term781 A _66637 _66639) = (_66637 = _66639).
Proof. exact (@lem5108992 (_66637 = _66639)). Qed.
Lemma lem5108994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5108995 {A : Type'} (_66637 : A) (_66639 : A) : (term782 A _66637 _66639) = (term783 A _66637 _66639).
Proof. exact (MK_COMB (@lem5108994) (@lem5108993 A _66637 _66639)). Qed.
Lemma lem5108997 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5108998 {A : Type'} (_66636 : type1402 A) (_66638 : type1402 A) : (term784 A _66636 _66638) = (_66636 = _66638).
Proof. exact (@lem5108997 (_66636 = _66638)). Qed.
Lemma lem5108999 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) : (term780 A _66637 _66639 _66636 _66638) = (term785 A _66637 _66639 _66636 _66638).
Proof. exact (MK_COMB (@lem5108995 A _66637 _66639) (@lem5108998 A _66636 _66638)). Qed.
Lemma lem5109000 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) : (term779 A _66637 _66639 _66636 _66638) = (term785 A _66637 _66639 _66636 _66638).
Proof. exact (TRANS (@lem5108990 A _66637 _66639 _66636 _66638) (@lem5108999 A _66637 _66639 _66636 _66638)). Qed.
Lemma lem5109001 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5109002 {A : Type'} (_66637 : A) (_66639 : A) (_66636 : type1402 A) (_66638 : type1402 A) : (term786 A _66637 _66639 _66636 _66638) = (term787 A _66637 _66639 _66636 _66638).
Proof. exact (MK_COMB (@lem5109001) (@lem5109000 A _66637 _66639 _66636 _66638)). Qed.
Lemma lem5109003 {A : Type'} (_66636 : type1402 A) (_66637 : A) (_66638 : type1402 A) (_66639 : A) : ((@I (A -> A -> Prop) _66636 _66637) = (@I (A -> A -> Prop) _66638 _66639)) = ((@I (A -> A -> Prop) _66636 _66637) = (@I (A -> A -> Prop) _66638 _66639)).
Proof. exact (eq_refl ((@I (A -> A -> Prop) _66636 _66637) = (@I (A -> A -> Prop) _66638 _66639))). Qed.
Lemma lem5109004 {A : Type'} (_66636 : type1402 A) (_66637 : A) (_66638 : type1402 A) (_66639 : A) : (term777 A _66636 _66637 _66638 _66639) = (term788 A _66636 _66637 _66638 _66639).
Proof. exact (MK_COMB (@lem5109002 A _66637 _66639 _66636 _66638) (@lem5109003 A _66636 _66637 _66638 _66639)). Qed.
Lemma lem5109005 {A : Type'} (_66636 : type1402 A) (_66637 : A) (_66638 : type1402 A) (_66639 : A) : (term773 A _66637 _66639 _66636 _66638) = (term788 A _66636 _66637 _66638 _66639).
Proof. exact (TRANS (@lem5108987 A _66636 _66637 _66638 _66639) (@lem5109004 A _66636 _66637 _66638 _66639)). Qed.
Lemma lem5109007 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term701 A s x y) : term789 A x s y lt2.
Proof. exact (conj (@lem5108885 A s x y h1) (@lem5108894 A lt2)). Qed.
Lemma lem5109009 {A : Type'} (_66636 : type1402 A) (_66637 : A) (_66638 : type1402 A) (_66639 : A) : term788 A _66636 _66637 _66638 _66639.
Proof. exact (EQ_MP (@lem5109005 A _66636 _66637 _66638 _66639) (@lem5108984 A _66637 _66639 _66636 _66638)). Qed.
Lemma lem5109010 {A : Type'} (_66636 : type1402 A) (_66637 : A) (_66638 : type1402 A) (_66639 : A) : term788 A _66636 _66637 _66638 _66639.
Proof. exact (@lem5109009 A _66636 _66637 _66638 _66639). Qed.
Lemma lem5109011 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (y : nat) : term790 A x lt2 s y.
Proof. exact (@lem5109010 A lt2 (@I (nat -> A) s x) lt2 (@I (nat -> A) s y)). Qed.
Lemma lem5109014 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term701 A s x y) : (term578 A lt2 s x) = (term578 A lt2 s y).
Proof. exact (@lem5109011 A x lt2 s y (@lem5109007 A lt2 s x y h1)). Qed.
Lemma lem5109015 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term701 A s x y) : (term578 A lt2 s x) = (term578 A lt2 s y).
Proof. exact (@lem5109014 A lt2 s x y h1). Qed.
Lemma lem5109016 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term701 A s x y) : term791 A x lt2 s y.
Proof. exact (fun h0 : term792 A x lt2 s y => @lem5109015 A lt2 s x y h1). Qed.
Lemma lem5109018 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5109019 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (y : nat) : (term791 A x lt2 s y) = ((term578 A lt2 s x) = (term578 A lt2 s y)).
Proof. exact (@lem5109018 ((term578 A lt2 s x) = (term578 A lt2 s y))). Qed.
Lemma lem5109020 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term701 A s x y) : (term578 A lt2 s x) = (term578 A lt2 s y).
Proof. exact (EQ_MP (@lem5109019 A x lt2 s y) (@lem5109016 A lt2 s x y h1)). Qed.
Lemma lem5109023 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (y : nat) (h1 : term793 A lt2 s y) : term793 A lt2 s y.
Proof. exact (h1). Qed.
Lemma lem5109024 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (y : nat) (h1 : term793 A lt2 s y) : term794 A lt2 s y.
Proof. exact (fun h0 : term795 A lt2 s y => @lem5109023 A lt2 s y h1). Qed.
Lemma lem5109026 (p : Prop) : (term796 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5109027 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (y : nat) : (term794 A lt2 s y) = (term793 A lt2 s y).
Proof. exact (@lem5109026 (term795 A lt2 s y)). Qed.
Lemma lem5109028 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (y : nat) (h1 : term793 A lt2 s y) : term793 A lt2 s y.
Proof. exact (EQ_MP (@lem5109027 A lt2 s y) (@lem5109024 A lt2 s y h1)). Qed.
Lemma lem5109046 (q : Prop) (p : Prop) (r : Prop) : (term45 p q r) = (term45 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5109047 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term754 A _66590 _66591 _66588 _66589) = (term797 A _66591 _66590 _66588 _66589).
Proof. exact (@lem5109046 (@I (A -> Prop) _66590 _66591) (term798 A _66588 _66590) (term799 A _66588 _66589)). Qed.
Lemma lem5109065 {A : Type'} (_66589 : A) (_66591 : A) : (term771 A _66589 _66591) = (term771 A _66589 _66591).
Proof. exact (eq_refl (term771 A _66589 _66591)). Qed.
Lemma lem5109066 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term756 A _66590 _66591 _66588 _66589) = (term800 A _66591 _66590 _66588 _66589).
Proof. exact (MK_COMB (@lem5109065 A _66589 _66591) (@lem5109047 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109070 (q : Prop) (p : Prop) (r : Prop) : (term45 p q r) = (term45 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5109071 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term800 A _66591 _66590 _66588 _66589) = (term801 A _66591 _66590 _66588 _66589).
Proof. exact (@lem5109070 (@I (A -> Prop) _66590 _66591) (term774 A _66589 _66591) (term802 A _66590 _66588 _66589)). Qed.
Lemma lem5109101 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term756 A _66590 _66591 _66588 _66589) = (term801 A _66591 _66590 _66588 _66589).
Proof. exact (TRANS (@lem5109066 A _66591 _66590 _66588 _66589) (@lem5109071 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5109103 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term803 A _66590 _66591 _66588 _66589) = (term804 A _66591 _66590 _66588 _66589).
Proof. exact (MK_COMB (@lem5109102) (@lem5109101 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109107 (q : Prop) (p : Prop) (r : Prop) : (term45 p q r) = (term45 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5109108 {A : Type'} (_66589 : A) (_66588 : A -> Prop) (_66590 : A -> Prop) (_66591 : A) : (term805 A _66589 _66588 _66590 _66591) = (term806 A _66589 _66588 _66590 _66591).
Proof. exact (@lem5109107 (term774 A _66589 _66591) (term799 A _66588 _66589) (term807 A _66588 _66590 _66591)). Qed.
Lemma lem5109124 (q : Prop) (p : Prop) (r : Prop) : (term45 p q r) = (term45 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5109125 {A : Type'} (_66588 : A -> Prop) (_66589 : A) (_66590 : A -> Prop) (_66591 : A) : (term808 A _66589 _66588 _66590 _66591) = (term809 A _66588 _66589 _66590 _66591).
Proof. exact (@lem5109124 (term798 A _66588 _66590) (term799 A _66588 _66589) (@I (A -> Prop) _66590 _66591)). Qed.
Lemma lem5109141 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5109142 {A : Type'} (_66590 : A -> Prop) (_66591 : A) (_66588 : A -> Prop) (_66589 : A) : (term810 A _66588 _66589 _66590 _66591) = (term751 A _66590 _66591 _66588 _66589).
Proof. exact (@lem5109141 (@I (A -> Prop) _66590 _66591) (term799 A _66588 _66589)). Qed.
Lemma lem5109148 {A : Type'} (_66588 : A -> Prop) (_66590 : A -> Prop) : (term811 A _66588 _66590) = (term811 A _66588 _66590).
Proof. exact (eq_refl (term811 A _66588 _66590)). Qed.
Lemma lem5109149 {A : Type'} (_66590 : A -> Prop) (_66591 : A) (_66588 : A -> Prop) (_66589 : A) : (term809 A _66588 _66589 _66590 _66591) = (term754 A _66590 _66591 _66588 _66589).
Proof. exact (MK_COMB (@lem5109148 A _66588 _66590) (@lem5109142 A _66590 _66591 _66588 _66589)). Qed.
Lemma lem5109153 (q : Prop) (p : Prop) (r : Prop) : (term45 p q r) = (term45 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5109154 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term754 A _66590 _66591 _66588 _66589) = (term797 A _66591 _66590 _66588 _66589).
Proof. exact (@lem5109153 (@I (A -> Prop) _66590 _66591) (term798 A _66588 _66590) (term799 A _66588 _66589)). Qed.
Lemma lem5109172 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term809 A _66588 _66589 _66590 _66591) = (term797 A _66591 _66590 _66588 _66589).
Proof. exact (TRANS (@lem5109149 A _66590 _66591 _66588 _66589) (@lem5109154 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109173 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term808 A _66589 _66588 _66590 _66591) = (term797 A _66591 _66590 _66588 _66589).
Proof. exact (TRANS (@lem5109125 A _66588 _66589 _66590 _66591) (@lem5109172 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109174 {A : Type'} (_66589 : A) (_66591 : A) : (term771 A _66589 _66591) = (term771 A _66589 _66591).
Proof. exact (eq_refl (term771 A _66589 _66591)). Qed.
Lemma lem5109175 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term806 A _66589 _66588 _66590 _66591) = (term800 A _66591 _66590 _66588 _66589).
Proof. exact (MK_COMB (@lem5109174 A _66589 _66591) (@lem5109173 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109179 (q : Prop) (p : Prop) (r : Prop) : (term45 p q r) = (term45 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5109180 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term800 A _66591 _66590 _66588 _66589) = (term801 A _66591 _66590 _66588 _66589).
Proof. exact (@lem5109179 (@I (A -> Prop) _66590 _66591) (term774 A _66589 _66591) (term802 A _66590 _66588 _66589)). Qed.
Lemma lem5109210 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term806 A _66589 _66588 _66590 _66591) = (term801 A _66591 _66590 _66588 _66589).
Proof. exact (TRANS (@lem5109175 A _66591 _66590 _66588 _66589) (@lem5109180 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109211 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term805 A _66589 _66588 _66590 _66591) = (term801 A _66591 _66590 _66588 _66589).
Proof. exact (TRANS (@lem5109108 A _66589 _66588 _66590 _66591) (@lem5109210 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109212 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : ((term756 A _66590 _66591 _66588 _66589) = (term805 A _66589 _66588 _66590 _66591)) = ((term801 A _66591 _66590 _66588 _66589) = (term801 A _66591 _66590 _66588 _66589)).
Proof. exact (MK_COMB (@lem5109103 A _66591 _66590 _66588 _66589) (@lem5109211 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109214 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5109215 (x : Prop) : (x = x) = True.
Proof. exact (@lem5109214 Prop x). Qed.
Lemma lem5109216 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : ((term801 A _66591 _66590 _66588 _66589) = (term801 A _66591 _66590 _66588 _66589)) = True.
Proof. exact (@lem5109215 (term801 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109217 {A : Type'} (_66589 : A) (_66588 : A -> Prop) (_66590 : A -> Prop) (_66591 : A) : ((term756 A _66590 _66591 _66588 _66589) = (term805 A _66589 _66588 _66590 _66591)) = True.
Proof. exact (TRANS (@lem5109212 A _66591 _66590 _66588 _66589) (@lem5109216 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109218 {A : Type'} (_66589 : A) (_66588 : A -> Prop) (_66590 : A -> Prop) (_66591 : A) : True = ((term756 A _66590 _66591 _66588 _66589) = (term805 A _66589 _66588 _66590 _66591)).
Proof. exact (SYM (@lem5109217 A _66589 _66588 _66590 _66591)). Qed.
Lemma lem5109219 {A : Type'} (_66589 : A) (_66588 : A -> Prop) (_66590 : A -> Prop) (_66591 : A) : (term756 A _66590 _66591 _66588 _66589) = (term805 A _66589 _66588 _66590 _66591).
Proof. exact (EQ_MP (@lem5109218 A _66589 _66588 _66590 _66591) (@lem0)). Qed.
Lemma lem5109220 {A : Type'} (_66589 : A) (_66588 : A -> Prop) (_66590 : A -> Prop) (_66591 : A) : term805 A _66589 _66588 _66590 _66591.
Proof. exact (EQ_MP (@lem5109219 A _66589 _66588 _66590 _66591) (@lem5108641 A _66590 _66591 _66588 _66589)). Qed.
Lemma lem5109222 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5109223 {A : Type'} (_66590 : A -> Prop) (_66591 : A) (_66588 : A -> Prop) (_66589 : A) : (term805 A _66589 _66588 _66590 _66591) = (term812 A _66590 _66591 _66588 _66589).
Proof. exact (@lem5109222 (term813 A _66589 _66588 _66590 _66591) (term799 A _66588 _66589)). Qed.
Lemma lem5109225 (a : Prop) (b : Prop) : (term605 a b) = (term606 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5109226 {A : Type'} (_66589 : A) (_66588 : A -> Prop) (_66590 : A -> Prop) (_66591 : A) : (term814 A _66589 _66588 _66590 _66591) = (term815 A _66589 _66588 _66590 _66591).
Proof. exact (@lem5109225 (term774 A _66589 _66591) (term807 A _66588 _66590 _66591)). Qed.
Lemma lem5109228 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5109229 {A : Type'} (_66589 : A) (_66591 : A) : (term781 A _66589 _66591) = (_66589 = _66591).
Proof. exact (@lem5109228 (_66589 = _66591)). Qed.
Lemma lem5109230 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5109231 {A : Type'} (_66589 : A) (_66591 : A) : (term782 A _66589 _66591) = (term783 A _66589 _66591).
Proof. exact (MK_COMB (@lem5109230) (@lem5109229 A _66589 _66591)). Qed.
Lemma lem5109233 (a : Prop) (b : Prop) : (term605 a b) = (term606 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5109234 {A : Type'} (_66588 : A -> Prop) (_66590 : A -> Prop) (_66591 : A) : (term816 A _66588 _66590 _66591) = (term817 A _66588 _66590 _66591).
Proof. exact (@lem5109233 (term798 A _66588 _66590) (@I (A -> Prop) _66590 _66591)). Qed.
Lemma lem5109236 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5109237 {A : Type'} (_66588 : A -> Prop) (_66590 : A -> Prop) : (term818 A _66588 _66590) = (_66588 = _66590).
Proof. exact (@lem5109236 (_66588 = _66590)). Qed.
Lemma lem5109238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5109239 {A : Type'} (_66588 : A -> Prop) (_66590 : A -> Prop) : (term819 A _66588 _66590) = (term820 A _66588 _66590).
Proof. exact (MK_COMB (@lem5109238) (@lem5109237 A _66588 _66590)). Qed.
Lemma lem5109240 {A : Type'} (_66590 : A -> Prop) (_66591 : A) : (term799 A _66590 _66591) = (term799 A _66590 _66591).
Proof. exact (eq_refl (term799 A _66590 _66591)). Qed.
Lemma lem5109241 {A : Type'} (_66588 : A -> Prop) (_66590 : A -> Prop) (_66591 : A) : (term817 A _66588 _66590 _66591) = (term821 A _66588 _66590 _66591).
Proof. exact (MK_COMB (@lem5109239 A _66588 _66590) (@lem5109240 A _66590 _66591)). Qed.
Lemma lem5109242 {A : Type'} (_66588 : A -> Prop) (_66590 : A -> Prop) (_66591 : A) : (term816 A _66588 _66590 _66591) = (term821 A _66588 _66590 _66591).
Proof. exact (TRANS (@lem5109234 A _66588 _66590 _66591) (@lem5109241 A _66588 _66590 _66591)). Qed.
Lemma lem5109243 {A : Type'} (_66589 : A) (_66588 : A -> Prop) (_66590 : A -> Prop) (_66591 : A) : (term815 A _66589 _66588 _66590 _66591) = (term822 A _66589 _66588 _66590 _66591).
Proof. exact (MK_COMB (@lem5109231 A _66589 _66591) (@lem5109242 A _66588 _66590 _66591)). Qed.
Lemma lem5109244 {A : Type'} (_66589 : A) (_66588 : A -> Prop) (_66590 : A -> Prop) (_66591 : A) : (term814 A _66589 _66588 _66590 _66591) = (term822 A _66589 _66588 _66590 _66591).
Proof. exact (TRANS (@lem5109226 A _66589 _66588 _66590 _66591) (@lem5109243 A _66589 _66588 _66590 _66591)). Qed.
Lemma lem5109245 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5109246 {A : Type'} (_66589 : A) (_66588 : A -> Prop) (_66590 : A -> Prop) (_66591 : A) : (term823 A _66589 _66588 _66590 _66591) = (term824 A _66589 _66588 _66590 _66591).
Proof. exact (MK_COMB (@lem5109245) (@lem5109244 A _66589 _66588 _66590 _66591)). Qed.
Lemma lem5109247 {A : Type'} (_66588 : A -> Prop) (_66589 : A) : (term799 A _66588 _66589) = (term799 A _66588 _66589).
Proof. exact (eq_refl (term799 A _66588 _66589)). Qed.
Lemma lem5109248 {A : Type'} (_66590 : A -> Prop) (_66591 : A) (_66588 : A -> Prop) (_66589 : A) : (term812 A _66590 _66591 _66588 _66589) = (term825 A _66590 _66591 _66588 _66589).
Proof. exact (MK_COMB (@lem5109246 A _66589 _66588 _66590 _66591) (@lem5109247 A _66588 _66589)). Qed.
Lemma lem5109249 {A : Type'} (_66590 : A -> Prop) (_66591 : A) (_66588 : A -> Prop) (_66589 : A) : (term805 A _66589 _66588 _66590 _66591) = (term825 A _66590 _66591 _66588 _66589).
Proof. exact (TRANS (@lem5109223 A _66590 _66591 _66588 _66589) (@lem5109248 A _66590 _66591 _66588 _66589)). Qed.
Lemma lem5109251 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term793 A lt2 s y) (h2 : term701 A s x y) : term826 A x lt2 s y.
Proof. exact (conj (@lem5109020 A lt2 s x y h2) (@lem5109028 A lt2 s y h1)). Qed.
Lemma lem5109252 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term793 A lt2 s y) (h2 : term701 A s x y) : term827 A x lt2 s y.
Proof. exact (conj (@lem5108878 A s y) (@lem5109251 A lt2 s x y h1 h2)). Qed.
Lemma lem5109254 {A : Type'} (_66590 : A -> Prop) (_66591 : A) (_66588 : A -> Prop) (_66589 : A) : term825 A _66590 _66591 _66588 _66589.
Proof. exact (EQ_MP (@lem5109249 A _66590 _66591 _66588 _66589) (@lem5109220 A _66589 _66588 _66590 _66591)). Qed.
Lemma lem5109255 {A : Type'} (_66590 : A -> Prop) (_66591 : A) (_66588 : A -> Prop) (_66589 : A) : term825 A _66590 _66591 _66588 _66589.
Proof. exact (@lem5109254 A _66590 _66591 _66588 _66589). Qed.
Lemma lem5109256 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (y : nat) : term828 A lt2 x s y.
Proof. exact (@lem5109255 A (term578 A lt2 s y) (@I (nat -> A) s y) (term578 A lt2 s x) (@I (nat -> A) s y)). Qed.
Lemma lem5109259 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term793 A lt2 s y) (h2 : term701 A s x y) : term582 A lt2 x s y.
Proof. exact (@lem5109256 A lt2 x s y (@lem5109252 A lt2 s x y h1 h2)). Qed.
Lemma lem5109260 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term793 A lt2 s y) (h2 : term701 A s x y) : term829 A lt2 x s y.
Proof. exact (fun h0 : term580 A lt2 x s y => @lem5109259 A lt2 s x y h1 h2). Qed.
Lemma lem5109262 (p : Prop) : (term796 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5109263 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (y : nat) : (term829 A lt2 x s y) = (term582 A lt2 x s y).
Proof. exact (@lem5109262 (term580 A lt2 x s y)). Qed.
Lemma lem5109264 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term793 A lt2 s y) (h2 : term701 A s x y) : term582 A lt2 x s y.
Proof. exact (EQ_MP (@lem5109263 A lt2 x s y) (@lem5109260 A lt2 s x y h1 h2)). Qed.
Lemma lem5109266 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5109269 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66569 : nat) (_66570 : nat) : (term724 A lt2 _66570 s _66569) = (term830 A lt2 s _66569 _66570).
Proof. exact (@lem5109266 (term580 A lt2 _66570 s _66569) (term721 _66569 _66570)). Qed.
Lemma lem5109272 {A : Type'} (_66569 : nat) (_66570 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term830 A lt2 s _66569 _66570.
Proof. exact (EQ_MP (@lem5109269 A lt2 s _66569 _66570) (@lem5108558 A _66570 _66569 lt2 s h1)). Qed.
Lemma lem5109273 {A : Type'} (y : nat) (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term830 A lt2 s y x.
Proof. exact (@lem5109272 A y x lt2 s h1). Qed.
Lemma lem5109276 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term62 A lt2 s) (h2 : term793 A lt2 s y) (h3 : term701 A s x y) : term721 y x.
Proof. exact (@lem5109273 A y x lt2 s h1 (@lem5109264 A lt2 s x y h2 h3)). Qed.
Lemma lem5109277 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term62 A lt2 s) (h2 : term793 A lt2 s y) (h3 : term701 A s x y) : term831 y x.
Proof. exact (fun h0 : term719 y x => @lem5109276 A lt2 s x y h1 h2 h3). Qed.
Lemma lem5109279 (p : Prop) : (term796 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5109280 (y : nat) (x : nat) : (term831 y x) = (term721 y x).
Proof. exact (@lem5109279 (term719 y x)). Qed.
Lemma lem5109281 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term62 A lt2 s) (h2 : term793 A lt2 s y) (h3 : term701 A s x y) : term721 y x.
Proof. exact (EQ_MP (@lem5109280 y x) (@lem5109277 A lt2 s x y h1 h2 h3)). Qed.
Lemma lem5109283 {A : Type'} (s : nat -> A) (x : nat) (y : nat) (h1 : term701 A s x y) : term738 x y.
Proof. exact (proj2 (@lem5108097 A s x y h1)). Qed.
Lemma lem5109284 {A : Type'} (s : nat -> A) (x : nat) (y : nat) (h1 : term701 A s x y) : term832 x y.
Proof. exact (fun h0 : x = y => @lem5109283 A s x y h1). Qed.
Lemma lem5109286 (p : Prop) : (term796 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5109287 (x : nat) (y : nat) : (term832 x y) = (term738 x y).
Proof. exact (@lem5109286 (x = y)). Qed.
Lemma lem5109288 {A : Type'} (s : nat -> A) (x : nat) (y : nat) (h1 : term701 A s x y) : term738 x y.
Proof. exact (EQ_MP (@lem5109287 x y) (@lem5109284 A s x y h1)). Qed.
Lemma lem5109290 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5109291 (_66571 : nat) (_66572 : nat) : (term733 _66571 _66572) = (term833 _66571 _66572).
Proof. exact (@lem5109290 (term732 _66571 _66572) (term719 _66571 _66572)). Qed.
Lemma lem5109293 (a : Prop) (b : Prop) : (term605 a b) = (term606 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5109294 (_66571 : nat) (_66572 : nat) : (term834 _66571 _66572) = (term835 _66571 _66572).
Proof. exact (@lem5109293 (term719 _66572 _66571) (_66571 = _66572)). Qed.
Lemma lem5109295 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5109296 (_66571 : nat) (_66572 : nat) : (term836 _66571 _66572) = (term837 _66571 _66572).
Proof. exact (MK_COMB (@lem5109295) (@lem5109294 _66571 _66572)). Qed.
Lemma lem5109297 (_66571 : nat) (_66572 : nat) : (term719 _66571 _66572) = (term719 _66571 _66572).
Proof. exact (eq_refl (term719 _66571 _66572)). Qed.
Lemma lem5109298 (_66571 : nat) (_66572 : nat) : (term833 _66571 _66572) = (term838 _66571 _66572).
Proof. exact (MK_COMB (@lem5109296 _66571 _66572) (@lem5109297 _66571 _66572)). Qed.
Lemma lem5109299 (_66571 : nat) (_66572 : nat) : (term733 _66571 _66572) = (term838 _66571 _66572).
Proof. exact (TRANS (@lem5109291 _66571 _66572) (@lem5109298 _66571 _66572)). Qed.
Lemma lem5109301 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term62 A lt2 s) (h2 : term793 A lt2 s y) (h3 : term701 A s x y) : term835 x y.
Proof. exact (conj (@lem5109281 A lt2 s x y h1 h2 h3) (@lem5109288 A s x y h3)). Qed.
Lemma lem5109303 (_66571 : nat) (_66572 : nat) (h1 : term636) : term838 _66571 _66572.
Proof. exact (EQ_MP (@lem5109299 _66571 _66572) (@lem5108568 _66571 _66572 h1)). Qed.
Lemma lem5109304 (x : nat) (y : nat) (h1 : term636) : term838 x y.
Proof. exact (@lem5109303 x y h1). Qed.
Lemma lem5109307 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term62 A lt2 s) (h2 : term636) (h3 : term793 A lt2 s y) (h4 : term701 A s x y) : term719 x y.
Proof. exact (@lem5109304 x y h2 (@lem5109301 A lt2 s x y h1 h3 h4)). Qed.
Lemma lem5109308 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term62 A lt2 s) (h2 : term636) (h3 : term793 A lt2 s y) (h4 : term701 A s x y) : term839 x y.
Proof. exact (fun h0 : term721 x y => @lem5109307 A lt2 s x y h1 h2 h3 h4). Qed.
Lemma lem5109310 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5109311 (x : nat) (y : nat) : (term839 x y) = (term719 x y).
Proof. exact (@lem5109310 (term719 x y)). Qed.
Lemma lem5109312 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term62 A lt2 s) (h2 : term636) (h3 : term793 A lt2 s y) (h4 : term701 A s x y) : term719 x y.
Proof. exact (EQ_MP (@lem5109311 x y) (@lem5109308 A lt2 s x y h1 h2 h3 h4)). Qed.
Lemma lem5109318 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5109319 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66569 : nat) (_66570 : nat) : (term724 A lt2 _66570 s _66569) = (term840 A lt2 s _66569 _66570).
Proof. exact (@lem5109318 (term580 A lt2 _66570 s _66569) (term721 _66569 _66570)). Qed.
Lemma lem5109325 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5109326 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66569 : nat) (_66570 : nat) : (term841 A lt2 _66570 s _66569) = (term842 A lt2 s _66569 _66570).
Proof. exact (MK_COMB (@lem5109325) (@lem5109319 A lt2 s _66569 _66570)). Qed.
Lemma lem5109332 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66569 : nat) (_66570 : nat) : (term840 A lt2 s _66569 _66570) = (term840 A lt2 s _66569 _66570).
Proof. exact (eq_refl (term840 A lt2 s _66569 _66570)). Qed.
Lemma lem5109333 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66569 : nat) (_66570 : nat) : ((term724 A lt2 _66570 s _66569) = (term840 A lt2 s _66569 _66570)) = ((term840 A lt2 s _66569 _66570) = (term840 A lt2 s _66569 _66570)).
Proof. exact (MK_COMB (@lem5109326 A lt2 s _66569 _66570) (@lem5109332 A lt2 s _66569 _66570)). Qed.
Lemma lem5109335 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5109336 (x : Prop) : (x = x) = True.
Proof. exact (@lem5109335 Prop x). Qed.
Lemma lem5109337 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66569 : nat) (_66570 : nat) : ((term840 A lt2 s _66569 _66570) = (term840 A lt2 s _66569 _66570)) = True.
Proof. exact (@lem5109336 (term840 A lt2 s _66569 _66570)). Qed.
Lemma lem5109338 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66569 : nat) (_66570 : nat) : ((term724 A lt2 _66570 s _66569) = (term840 A lt2 s _66569 _66570)) = True.
Proof. exact (TRANS (@lem5109333 A lt2 s _66569 _66570) (@lem5109337 A lt2 s _66569 _66570)). Qed.
Lemma lem5109339 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66569 : nat) (_66570 : nat) : True = ((term724 A lt2 _66570 s _66569) = (term840 A lt2 s _66569 _66570)).
Proof. exact (SYM (@lem5109338 A lt2 s _66569 _66570)). Qed.
Lemma lem5109340 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66569 : nat) (_66570 : nat) : (term724 A lt2 _66570 s _66569) = (term840 A lt2 s _66569 _66570).
Proof. exact (EQ_MP (@lem5109339 A lt2 s _66569 _66570) (@lem0)). Qed.
Lemma lem5109341 {A : Type'} (_66569 : nat) (_66570 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term840 A lt2 s _66569 _66570.
Proof. exact (EQ_MP (@lem5109340 A lt2 s _66569 _66570) (@lem5108558 A _66570 _66569 lt2 s h1)). Qed.
Lemma lem5109343 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5109344 {A : Type'} (lt2 : type1402 A) (_66570 : nat) (s : nat -> A) (_66569 : nat) : (term840 A lt2 s _66569 _66570) = (term843 A lt2 _66570 s _66569).
Proof. exact (@lem5109343 (term721 _66569 _66570) (term580 A lt2 _66570 s _66569)). Qed.
Lemma lem5109346 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5109347 (_66569 : nat) (_66570 : nat) : (term844 _66569 _66570) = (term719 _66569 _66570).
Proof. exact (@lem5109346 (term719 _66569 _66570)). Qed.
Lemma lem5109348 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5109349 (_66569 : nat) (_66570 : nat) : (term845 _66569 _66570) = (term846 _66569 _66570).
Proof. exact (MK_COMB (@lem5109348) (@lem5109347 _66569 _66570)). Qed.
Lemma lem5109350 {A : Type'} (lt2 : type1402 A) (_66570 : nat) (s : nat -> A) (_66569 : nat) : (term580 A lt2 _66570 s _66569) = (term580 A lt2 _66570 s _66569).
Proof. exact (eq_refl (term580 A lt2 _66570 s _66569)). Qed.
Lemma lem5109351 {A : Type'} (lt2 : type1402 A) (_66570 : nat) (s : nat -> A) (_66569 : nat) : (term843 A lt2 _66570 s _66569) = (term847 A lt2 _66570 s _66569).
Proof. exact (MK_COMB (@lem5109349 _66569 _66570) (@lem5109350 A lt2 _66570 s _66569)). Qed.
Lemma lem5109352 {A : Type'} (lt2 : type1402 A) (_66570 : nat) (s : nat -> A) (_66569 : nat) : (term840 A lt2 s _66569 _66570) = (term847 A lt2 _66570 s _66569).
Proof. exact (TRANS (@lem5109344 A lt2 _66570 s _66569) (@lem5109351 A lt2 _66570 s _66569)). Qed.
Lemma lem5109355 {A : Type'} (_66570 : nat) (_66569 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term847 A lt2 _66570 s _66569.
Proof. exact (EQ_MP (@lem5109352 A lt2 _66570 s _66569) (@lem5109341 A _66569 _66570 lt2 s h1)). Qed.
Lemma lem5109356 {A : Type'} (y : nat) (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term847 A lt2 y s x.
Proof. exact (@lem5109355 A y x lt2 s h1). Qed.
Lemma lem5109359 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term62 A lt2 s) (h2 : term636) (h3 : term793 A lt2 s y) (h4 : term701 A s x y) : term580 A lt2 y s x.
Proof. exact (@lem5109356 A y x lt2 s h1 (@lem5109312 A lt2 s x y h1 h2 h3 h4)). Qed.
Lemma lem5109360 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term62 A lt2 s) (h2 : term636) (h3 : term793 A lt2 s y) (h4 : term701 A s x y) : term595 A lt2 y s x.
Proof. exact (fun h0 : term582 A lt2 y s x => @lem5109359 A lt2 s x y h1 h2 h3 h4). Qed.
Lemma lem5109362 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5109363 {A : Type'} (lt2 : type1402 A) (y : nat) (s : nat -> A) (x : nat) : (term595 A lt2 y s x) = (term580 A lt2 y s x).
Proof. exact (@lem5109362 (term580 A lt2 y s x)). Qed.
Lemma lem5109364 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term62 A lt2 s) (h2 : term636) (h3 : term793 A lt2 s y) (h4 : term701 A s x y) : term580 A lt2 y s x.
Proof. exact (EQ_MP (@lem5109363 A lt2 y s x) (@lem5109360 A lt2 s x y h1 h2 h3 h4)). Qed.
Lemma lem5109382 (q : Prop) (p : Prop) (r : Prop) : (term45 p q r) = (term45 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5109383 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term754 A _66590 _66591 _66588 _66589) = (term797 A _66591 _66590 _66588 _66589).
Proof. exact (@lem5109382 (@I (A -> Prop) _66590 _66591) (term798 A _66588 _66590) (term799 A _66588 _66589)). Qed.
Lemma lem5109401 {A : Type'} (_66589 : A) (_66591 : A) : (term771 A _66589 _66591) = (term771 A _66589 _66591).
Proof. exact (eq_refl (term771 A _66589 _66591)). Qed.
Lemma lem5109402 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term756 A _66590 _66591 _66588 _66589) = (term800 A _66591 _66590 _66588 _66589).
Proof. exact (MK_COMB (@lem5109401 A _66589 _66591) (@lem5109383 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109406 (q : Prop) (p : Prop) (r : Prop) : (term45 p q r) = (term45 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5109407 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term800 A _66591 _66590 _66588 _66589) = (term801 A _66591 _66590 _66588 _66589).
Proof. exact (@lem5109406 (@I (A -> Prop) _66590 _66591) (term774 A _66589 _66591) (term802 A _66590 _66588 _66589)). Qed.
Lemma lem5109437 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term756 A _66590 _66591 _66588 _66589) = (term801 A _66591 _66590 _66588 _66589).
Proof. exact (TRANS (@lem5109402 A _66591 _66590 _66588 _66589) (@lem5109407 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109438 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5109439 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term803 A _66590 _66591 _66588 _66589) = (term804 A _66591 _66590 _66588 _66589).
Proof. exact (MK_COMB (@lem5109438) (@lem5109437 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109469 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term801 A _66591 _66590 _66588 _66589) = (term801 A _66591 _66590 _66588 _66589).
Proof. exact (eq_refl (term801 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109470 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : ((term756 A _66590 _66591 _66588 _66589) = (term801 A _66591 _66590 _66588 _66589)) = ((term801 A _66591 _66590 _66588 _66589) = (term801 A _66591 _66590 _66588 _66589)).
Proof. exact (MK_COMB (@lem5109439 A _66591 _66590 _66588 _66589) (@lem5109469 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109472 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5109473 (x : Prop) : (x = x) = True.
Proof. exact (@lem5109472 Prop x). Qed.
Lemma lem5109474 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : ((term801 A _66591 _66590 _66588 _66589) = (term801 A _66591 _66590 _66588 _66589)) = True.
Proof. exact (@lem5109473 (term801 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109475 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : ((term756 A _66590 _66591 _66588 _66589) = (term801 A _66591 _66590 _66588 _66589)) = True.
Proof. exact (TRANS (@lem5109470 A _66591 _66590 _66588 _66589) (@lem5109474 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109476 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : True = ((term756 A _66590 _66591 _66588 _66589) = (term801 A _66591 _66590 _66588 _66589)).
Proof. exact (SYM (@lem5109475 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109477 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term756 A _66590 _66591 _66588 _66589) = (term801 A _66591 _66590 _66588 _66589).
Proof. exact (EQ_MP (@lem5109476 A _66591 _66590 _66588 _66589) (@lem0)). Qed.
Lemma lem5109478 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : term801 A _66591 _66590 _66588 _66589.
Proof. exact (EQ_MP (@lem5109477 A _66591 _66590 _66588 _66589) (@lem5108641 A _66590 _66591 _66588 _66589)). Qed.
Lemma lem5109480 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5109481 {A : Type'} (_66588 : A -> Prop) (_66589 : A) (_66590 : A -> Prop) (_66591 : A) : (term801 A _66591 _66590 _66588 _66589) = (term848 A _66588 _66589 _66590 _66591).
Proof. exact (@lem5109480 (term849 A _66591 _66590 _66588 _66589) (@I (A -> Prop) _66590 _66591)). Qed.
Lemma lem5109483 (a : Prop) (b : Prop) : (term605 a b) = (term606 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5109484 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term850 A _66591 _66590 _66588 _66589) = (term851 A _66591 _66590 _66588 _66589).
Proof. exact (@lem5109483 (term774 A _66589 _66591) (term802 A _66590 _66588 _66589)). Qed.
Lemma lem5109486 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5109487 {A : Type'} (_66589 : A) (_66591 : A) : (term781 A _66589 _66591) = (_66589 = _66591).
Proof. exact (@lem5109486 (_66589 = _66591)). Qed.
Lemma lem5109488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5109489 {A : Type'} (_66589 : A) (_66591 : A) : (term782 A _66589 _66591) = (term783 A _66589 _66591).
Proof. exact (MK_COMB (@lem5109488) (@lem5109487 A _66589 _66591)). Qed.
Lemma lem5109491 (a : Prop) (b : Prop) : (term605 a b) = (term606 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5109492 {A : Type'} (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term852 A _66590 _66588 _66589) = (term853 A _66590 _66588 _66589).
Proof. exact (@lem5109491 (term798 A _66588 _66590) (term799 A _66588 _66589)). Qed.
Lemma lem5109494 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5109495 {A : Type'} (_66588 : A -> Prop) (_66590 : A -> Prop) : (term818 A _66588 _66590) = (_66588 = _66590).
Proof. exact (@lem5109494 (_66588 = _66590)). Qed.
Lemma lem5109496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5109497 {A : Type'} (_66588 : A -> Prop) (_66590 : A -> Prop) : (term819 A _66588 _66590) = (term820 A _66588 _66590).
Proof. exact (MK_COMB (@lem5109496) (@lem5109495 A _66588 _66590)). Qed.
Lemma lem5109499 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5109500 {A : Type'} (_66588 : A -> Prop) (_66589 : A) : (term854 A _66588 _66589) = (@I (A -> Prop) _66588 _66589).
Proof. exact (@lem5109499 (@I (A -> Prop) _66588 _66589)). Qed.
Lemma lem5109501 {A : Type'} (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term853 A _66590 _66588 _66589) = (term855 A _66590 _66588 _66589).
Proof. exact (MK_COMB (@lem5109497 A _66588 _66590) (@lem5109500 A _66588 _66589)). Qed.
Lemma lem5109502 {A : Type'} (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term852 A _66590 _66588 _66589) = (term855 A _66590 _66588 _66589).
Proof. exact (TRANS (@lem5109492 A _66590 _66588 _66589) (@lem5109501 A _66590 _66588 _66589)). Qed.
Lemma lem5109503 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term851 A _66591 _66590 _66588 _66589) = (term856 A _66591 _66590 _66588 _66589).
Proof. exact (MK_COMB (@lem5109489 A _66589 _66591) (@lem5109502 A _66590 _66588 _66589)). Qed.
Lemma lem5109504 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term850 A _66591 _66590 _66588 _66589) = (term856 A _66591 _66590 _66588 _66589).
Proof. exact (TRANS (@lem5109484 A _66591 _66590 _66588 _66589) (@lem5109503 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109505 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5109506 {A : Type'} (_66591 : A) (_66590 : A -> Prop) (_66588 : A -> Prop) (_66589 : A) : (term857 A _66591 _66590 _66588 _66589) = (term858 A _66591 _66590 _66588 _66589).
Proof. exact (MK_COMB (@lem5109505) (@lem5109504 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109507 {A : Type'} (_66590 : A -> Prop) (_66591 : A) : (@I (A -> Prop) _66590 _66591) = (@I (A -> Prop) _66590 _66591).
Proof. exact (eq_refl (@I (A -> Prop) _66590 _66591)). Qed.
Lemma lem5109508 {A : Type'} (_66588 : A -> Prop) (_66589 : A) (_66590 : A -> Prop) (_66591 : A) : (term848 A _66588 _66589 _66590 _66591) = (term859 A _66588 _66589 _66590 _66591).
Proof. exact (MK_COMB (@lem5109506 A _66591 _66590 _66588 _66589) (@lem5109507 A _66590 _66591)). Qed.
Lemma lem5109509 {A : Type'} (_66588 : A -> Prop) (_66589 : A) (_66590 : A -> Prop) (_66591 : A) : (term801 A _66591 _66590 _66588 _66589) = (term859 A _66588 _66589 _66590 _66591).
Proof. exact (TRANS (@lem5109481 A _66588 _66589 _66590 _66591) (@lem5109508 A _66588 _66589 _66590 _66591)). Qed.
Lemma lem5109511 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term62 A lt2 s) (h2 : term636) (h3 : term793 A lt2 s y) (h4 : term701 A s x y) : term860 A lt2 y s x.
Proof. exact (conj (@lem5108869 A lt2 s y) (@lem5109364 A lt2 s x y h1 h2 h3 h4)). Qed.
Lemma lem5109512 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term62 A lt2 s) (h2 : term636) (h3 : term793 A lt2 s y) (h4 : term701 A s x y) : term861 A lt2 y s x.
Proof. exact (conj (@lem5108860 A s x y h4) (@lem5109511 A lt2 s x y h1 h2 h3 h4)). Qed.
Lemma lem5109514 {A : Type'} (_66588 : A -> Prop) (_66589 : A) (_66590 : A -> Prop) (_66591 : A) : term859 A _66588 _66589 _66590 _66591.
Proof. exact (EQ_MP (@lem5109509 A _66588 _66589 _66590 _66591) (@lem5109478 A _66591 _66590 _66588 _66589)). Qed.
Lemma lem5109515 {A : Type'} (_66588 : A -> Prop) (_66589 : A) (_66590 : A -> Prop) (_66591 : A) : term859 A _66588 _66589 _66590 _66591.
Proof. exact (@lem5109514 A _66588 _66589 _66590 _66591). Qed.
Lemma lem5109516 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (y : nat) : term862 A x lt2 s y.
Proof. exact (@lem5109515 A (term578 A lt2 s y) (@I (nat -> A) s x) (term578 A lt2 s y) (@I (nat -> A) s y)). Qed.
Lemma lem5109519 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term62 A lt2 s) (h2 : term636) (h3 : term793 A lt2 s y) (h4 : term701 A s x y) : term795 A lt2 s y.
Proof. exact (@lem5109516 A x lt2 s y (@lem5109512 A lt2 s x y h1 h2 h3 h4)). Qed.
Lemma lem5109520 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term62 A lt2 s) (h2 : term636) (h3 : term701 A s x y) : term863 A lt2 s y.
Proof. exact (fun h0 : term793 A lt2 s y => @lem5109519 A lt2 s x y h1 h2 h0 h3). Qed.
Lemma lem5109522 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5109523 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (y : nat) : (term863 A lt2 s y) = (term795 A lt2 s y).
Proof. exact (@lem5109522 (term795 A lt2 s y)). Qed.
Lemma lem5109524 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term62 A lt2 s) (h2 : term636) (h3 : term701 A s x y) : term795 A lt2 s y.
Proof. exact (EQ_MP (@lem5109523 A lt2 s y) (@lem5109520 A lt2 s x y h1 h2 h3)). Qed.
Lemma lem5109527 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5109529 {A : Type'} (lt2 : type1402 A) (_66563 : A) : (term716 A lt2 _66563) = (term864 A lt2 _66563).
Proof. exact (@lem5109527 (term715 A lt2 _66563)). Qed.
Lemma lem5109532 {A : Type'} (_66563 : A) (lt2 : type1402 A) (h1 : term56 A lt2) : term864 A lt2 _66563.
Proof. exact (EQ_MP (@lem5109529 A lt2 _66563) (@lem5108536 A _66563 lt2 h1)). Qed.
Lemma lem5109533 {A : Type'} (_66563 : A) (lt2 : type1402 A) (h1 : term56 A lt2) : term864 A lt2 _66563.
Proof. exact (@lem5109532 A _66563 lt2 h1). Qed.
Lemma lem5109534 {A : Type'} (s : nat -> A) (y : nat) (lt2 : type1402 A) (h1 : term56 A lt2) : term865 A lt2 s y.
Proof. exact (@lem5109533 A (@I (nat -> A) s y) lt2 h1). Qed.
Lemma lem5109537 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term56 A lt2) (h2 : term62 A lt2 s) (h3 : term636) (h4 : term701 A s x y) : False.
Proof. exact (@lem5109534 A s y lt2 h1 (@lem5109524 A lt2 s x y h2 h3 h4)). Qed.
Lemma lem5109538 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term56 A lt2) (h2 : term62 A lt2 s) (h3 : term636) (h4 : term701 A s x y) : term619.
Proof. exact (fun h0 : ~ False => @lem5109537 A lt2 s x y h1 h2 h3 h4). Qed.
Lemma lem5109540 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5109541 : term619 = False.
Proof. exact (@lem5109540 False). Qed.
Lemma lem5109542 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term56 A lt2) (h2 : term62 A lt2 s) (h3 : term636) (h4 : term701 A s x y) : False.
Proof. exact (EQ_MP (@lem5109541) (@lem5109538 A lt2 s x y h1 h2 h3 h4)). Qed.
Lemma lem5109543 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (s : nat -> A) (x : nat) (y : nat) (h1 : term56 A lt2) (h2 : term228 A _66562) (h3 : term62 A lt2 s) (h4 : term636) (h5 : term701 A s x y) : False.
Proof. exact (ex_elim (@lem5107433 A _66562 h2) (fun y' : type417 A => fun h0 : term434 A _66562 y' => @lem5109542 A lt2 s x y h1 h3 h4 h5)). Qed.
Lemma lem5109544 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (s : nat -> A) (x : nat) (h1 : term56 A lt2) (h2 : term228 A _66562) (h3 : term62 A lt2 s) (h4 : term636) (h5 : term708 A s x) : False.
Proof. exact (ex_elim (@lem5107782 A s x h5) (fun y : nat => fun h0 : term707 A s x y => @lem5109543 A _66562 lt2 s x y h1 h2 h3 h4 h0)). Qed.
Lemma lem5109545 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term56 A lt2) (h2 : term228 A _66562) (h3 : term62 A lt2 s) (h4 : term636) (h5 : term629 A s) : False.
Proof. exact (ex_elim (@lem5107709 A s h5) (fun x : nat => fun h0 : term713 A s x => @lem5109544 A _66562 lt2 s x h1 h2 h3 h4 h0)). Qed.
Lemma lem5109546 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term56 A lt2) (h2 : term228 A _66562) (h3 : term62 A lt2 s) (h4 : term636) (h5 : term629 A s) : term636 = False.
Proof. exact (prop_ext (fun h6 : term636 => @lem5109545 A _66562 lt2 s h1 h2 h3 h4 h5) (fun h6 : False => @lem5107781 h4)). Qed.
Lemma lem5109547 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term56 A lt2) (h2 : term228 A _66562) (h3 : term62 A lt2 s) (h4 : term636) (h5 : term629 A s) : False.
Proof. exact (EQ_MP (@lem5109546 A _66562 lt2 s h1 h2 h3 h4 h5) (@lem5107781 h4)). Qed.
Lemma lem5109548 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term56 A lt2) (h2 : term228 A _66562) (h3 : term62 A lt2 s) (h4 : term636) (h5 : term629 A s) : (term56 A lt2) = False.
Proof. exact (prop_ext (fun h6 : term56 A lt2 => @lem5109547 A _66562 lt2 s h1 h2 h3 h4 h5) (fun h6 : False => @lem5107446 A lt2 h1)). Qed.
Lemma lem5109549 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term56 A lt2) (h2 : term228 A _66562) (h3 : term62 A lt2 s) (h4 : term636) (h5 : term629 A s) : False.
Proof. exact (EQ_MP (@lem5109548 A _66562 lt2 s h1 h2 h3 h4 h5) (@lem5107446 A lt2 h1)). Qed.
Lemma lem5109550 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term56 A lt2) (h2 : term228 A _66562) (h3 : term62 A lt2 s) (h4 : term629 A s) : term634.
Proof. exact (fun h0 : term636 => @lem5109549 A _66562 lt2 s h1 h2 h3 h0 h4). Qed.
Lemma lem5109551 : term634 = term635.
Proof. exact (@lem69 term636). Qed.
Lemma lem5109552 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term56 A lt2) (h2 : term228 A _66562) (h3 : term62 A lt2 s) (h4 : term629 A s) : term635.
Proof. exact (EQ_MP (@lem5109551) (@lem5109550 A _66562 lt2 s h1 h2 h3 h4)). Qed.
Lemma lem5109553 {A : Type'} (_66562 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term56 A lt2) (h2 : term228 A _66562) (h3 : term62 A lt2 s) : term639 A s.
Proof. exact (fun h0 : term629 A s => @lem5109552 A _66562 lt2 s h1 h2 h3 h0). Qed.
Lemma lem5109554 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (_66562 : type418 A) (h1 : term56 A lt2) (h2 : term228 A _66562) : term642 A lt2 s.
Proof. exact (fun h0 : term62 A lt2 s => @lem5109553 A _66562 lt2 s h1 h2 h0). Qed.
Lemma lem5109555 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (_66562 : type418 A) (h1 : term56 A lt2) (h2 : term228 A _66562) : term644 A lt2 s.
Proof. exact (fun h0 : term61 A lt2 s => @lem5109554 A s lt2 _66562 h1 h2). Qed.
Lemma lem5109556 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (_66562 : type418 A) (h1 : term56 A lt2) (h2 : term228 A _66562) : term666 A _66562 lt2 s.
Proof. exact (fun h0 : term154 A _66562 lt2 => @lem5109555 A s lt2 _66562 h1 h2). Qed.
Lemma lem5109557 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (_66562 : type418 A) (h1 : term56 A lt2) (h2 : term228 A _66562) : term667 A _66562 lt2 s.
Proof. exact (fun h0 : term58 A lt2 => @lem5109556 A s lt2 _66562 h1 h2). Qed.
Lemma lem5109558 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66562 : type418 A) (h1 : term228 A _66562) : term668 A _66562 lt2 s.
Proof. exact (fun h0 : term56 A lt2 => @lem5109557 A s lt2 _66562 h0 h1). Qed.
Lemma lem5109563 {A : Type'} (s : nat -> A) (_66562 : type418 A) (h1 : term228 A _66562) : term670 A _66562 s.
Proof. exact (fun lt2 : type1402 A => @lem5109558 A lt2 s _66562 h1). Qed.
Lemma lem5109568 {A : Type'} (_66562 : type418 A) (h1 : term228 A _66562) : term672 A _66562.
Proof. exact (fun s : nat -> A => @lem5109563 A s _66562 h1). Qed.
Lemma lem5109569 {A : Type'} (_66562 : type418 A) : term692 A _66562.
Proof. exact (fun h0 : term228 A _66562 => @lem5109568 A _66562 h0). Qed.
Lemma lem5109574 {A : Type'} : term694 A.
Proof. exact (fun _66562 : type418 A => @lem5109569 A _66562). Qed.
Lemma lem5109575 {A : Type'} : term656 A.
Proof. exact (EQ_MP (@lem5106807 A) (@lem5109574 A)). Qed.
Lemma lem5109576 {A : Type'} (s : nat -> A) : term866 A s.
Proof. exact (@lem5109575 A s). Qed.
Lemma lem5109577 {A : Type'} (s : nat -> A) : (term866 A s) = (term652 A s).
Proof. exact (eq_refl (term866 A s)). Qed.
Lemma lem5109578 {A : Type'} (s : nat -> A) : term652 A s.
Proof. exact (EQ_MP (@lem5109577 A s) (@lem5109576 A s)). Qed.
Lemma lem5109579 {A : Type'} (s : nat -> A) (lt2 : type1402 A) : term867 A s lt2.
Proof. exact (@lem5109578 A s lt2). Qed.
Lemma lem5109580 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term867 A s lt2) = (term630 A lt2 s).
Proof. exact (eq_refl (term867 A s lt2)). Qed.
Lemma lem5109581 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term630 A lt2 s.
Proof. exact (EQ_MP (@lem5109580 A lt2 s) (@lem5109579 A s lt2)). Qed.
Lemma lem5109583 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term630 A lt2 s.
Proof. exact (@lem5106086 A lt2 s (@lem5109581 A lt2 s)). Qed.
Lemma lem5109584 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (h1 : term56 A lt2) : term647 A lt2 s.
Proof. exact (@lem5109583 A lt2 s (@lem5103242 A lt2 h1)). Qed.
Lemma lem5109585 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (h1 : term58 A lt2) (h2 : term56 A lt2) : term645 A lt2 s.
Proof. exact (@lem5109584 A s lt2 h2 (@lem5103244 A lt2 h1)). Qed.
Lemma lem5109586 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) : term643 A lt2 s.
Proof. exact (@lem5109585 A s lt2 h1 h3 (@lem5103243 A lt2 h2)). Qed.
Lemma lem5109587 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term61 A lt2 s) : term641 A lt2 s.
Proof. exact (@lem5109586 A s lt2 h1 h2 h3 (@lem5103258 A lt2 s h4)). Qed.
Lemma lem5109588 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term638 A s.
Proof. exact (@lem5109587 A lt2 s h1 h2 h3 h5 (@lem5103259 A lt2 s h4)). Qed.
Lemma lem5109589 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) (h6 : term629 A s) : term634.
Proof. exact (@lem5109588 A lt2 s h1 h2 h3 h4 h5 (@lem5106070 A s h6)). Qed.
Lemma lem5109590 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) (h6 : term629 A s) : False.
Proof. exact (@lem5109589 A lt2 s h1 h2 h3 h4 h5 h6 (@lem96657)). Qed.
Lemma lem5109591 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) (h6 : term629 A s) : (term629 A s) = False.
Proof. exact (prop_ext (fun h7 : term629 A s => @lem5109590 A lt2 s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem5106070 A s h6)). Qed.
Lemma lem5109592 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) (h6 : term629 A s) : False.
Proof. exact (EQ_MP (@lem5109591 A lt2 s h1 h2 h3 h4 h5 h6) (@lem5106070 A s h6)). Qed.
Lemma lem5109593 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term628 A s.
Proof. exact (fun h0 : term629 A s => @lem5109592 A lt2 s h1 h2 h3 h4 h5 h0). Qed.
Lemma lem5109594 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term626 A s.
Proof. exact (EQ_MP (@lem5106069 A s) (@lem5109593 A lt2 s h1 h2 h3 h4 h5)). Qed.
Lemma lem5109595 {A : Type'} (s : nat -> A) (h1 : term627 A s) : term627 A s.
Proof. exact (h1). Qed.
Lemma lem5109596 {A : Type'} (s : nat -> A) (h1 : term627 A s) : term868 A s.
Proof. exact (@lem5109595 A s h1 (@UNIV nat)). Qed.
Lemma lem5109597 {A : Type'} (s : nat -> A) : (term868 A s) = (term869 A s).
Proof. exact (eq_refl (term868 A s)). Qed.
Lemma lem5109598 {A : Type'} (s : nat -> A) (h1 : term627 A s) : term869 A s.
Proof. exact (EQ_MP (@lem5109597 A s) (@lem5109596 A s h1)). Qed.
Lemma lem5109600 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem5109601 {A : Type'} (s : nat -> A) : (term870 A s) = (term871 A s).
Proof. exact (@lem5109600 (term869 A s)). Qed.
Lemma lem5109605 : (@INFINITE nat (@UNIV nat)) = True.
Proof. exact (EQ_MP (@lem5103198) (@lem4629194)). Qed.
Lemma lem5109606 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5109607 : term872 = (imp True).
Proof. exact (MK_COMB (@lem5109606) (@lem5109605)). Qed.
Lemma lem5109608 {A : Type'} (s : nat -> A) : (term873 A s) = (term873 A s).
Proof. exact (eq_refl (term873 A s)). Qed.
Lemma lem5109609 {A : Type'} (s : nat -> A) : (term869 A s) = (term874 A s).
Proof. exact (MK_COMB (@lem5109607) (@lem5109608 A s)). Qed.
Lemma lem5109611 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5109612 {A : Type'} (s : nat -> A) : (term874 A s) = (term873 A s).
Proof. exact (@lem5109611 (term873 A s)). Qed.
Lemma lem5109613 {A : Type'} (s : nat -> A) : (term869 A s) = (term873 A s).
Proof. exact (TRANS (@lem5109609 A s) (@lem5109612 A s)). Qed.
Lemma lem5109614 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5109615 {A : Type'} (s : nat -> A) : (term871 A s) = (term875 A s).
Proof. exact (MK_COMB (@lem5109614) (@lem5109613 A s)). Qed.
Lemma lem5109616 {A : Type'} (s : nat -> A) : (term870 A s) = (term875 A s).
Proof. exact (TRANS (@lem5109601 A s) (@lem5109615 A s)). Qed.
Lemma lem5109617 {A : Type'} (s : nat -> A) : (term875 A s) = (term870 A s).
Proof. exact (SYM (@lem5109616 A s)). Qed.
Lemma lem5109619 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term36 A s).
Proof. exact (EQ_MP (@lem5103196 A s) (@lem5103195 A s)). Qed.
Lemma lem5109620 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (term36 A s).
Proof. exact (@lem5109619 A s). Qed.
Lemma lem5109621 {A : Type'} (s : nat -> A) : (term873 A s) = (term876 A s).
Proof. exact (@lem5109620 A (@IMAGE nat A s (@UNIV nat))). Qed.
Lemma lem5109622 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5109623 {A : Type'} (s : nat -> A) : (term875 A s) = (term877 A s).
Proof. exact (MK_COMB (@lem5109622) (@lem5109621 A s)). Qed.
Lemma lem5109625 (t : Prop) : (term121 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem5109626 {A : Type'} (s : nat -> A) : (term877 A s) = (term878 A s).
Proof. exact (@lem5109625 (term878 A s)). Qed.
Lemma lem5109627 {A : Type'} (s : nat -> A) : (term875 A s) = (term878 A s).
Proof. exact (TRANS (@lem5109623 A s) (@lem5109626 A s)). Qed.
Lemma lem5109628 {A : Type'} (s : nat -> A) : (term878 A s) = (term875 A s).
Proof. exact (SYM (@lem5109627 A s)). Qed.
Lemma lem5109630 {A : Type'} (s : A -> Prop) : term31 A s.
Proof. exact (EQ_MP (@lem5103193 A s) (@lem5103192 A s)). Qed.
Lemma lem5109631 {A : Type'} (s : A -> Prop) : term31 A s.
Proof. exact (@lem5109630 A s). Qed.
Lemma lem5109632 {A : Type'} (s : nat -> A) : term879 A s.
Proof. exact (@lem5109631 A (@IMAGE nat A s (@UNIV nat))). Qed.
Lemma lem5109633 {A : Type'} (s : A -> Prop) : term880 A s.
Proof. exact (@lem3608316 A s). Qed.
Lemma lem5109634 {A : Type'} (s : A -> Prop) : (term880 A s) = (term881 A s).
Proof. exact (eq_refl (term880 A s)). Qed.
Lemma lem5109635 {A : Type'} (s : A -> Prop) : term881 A s.
Proof. exact (EQ_MP (@lem5109634 A s) (@lem5109633 A s)). Qed.
Lemma lem5109636 {A : Type'} (s : A -> Prop) (x : A) : term882 A s x.
Proof. exact (@lem5109635 A s x). Qed.
Lemma lem5109637 {A : Type'} (x : A) (s : A -> Prop) : (term882 A s x) = ((term883 A x s) = (@FINITE A s)).
Proof. exact (eq_refl (term882 A s x)). Qed.
Lemma lem5109655 {A : Type'} (x : A) (lt2 : type1402 A) (h1 : term57 A lt2) : term884 A lt2 x.
Proof. exact (@lem5103243 A lt2 h1 x). Qed.
Lemma lem5109656 {A : Type'} (lt2 : type1402 A) (x : A) : (term884 A lt2 x) = (term150 A lt2 x).
Proof. exact (eq_refl (term884 A lt2 x)). Qed.
Lemma lem5109657 {A : Type'} (x : A) (lt2 : type1402 A) (h1 : term57 A lt2) : term150 A lt2 x.
Proof. exact (EQ_MP (@lem5109656 A lt2 x) (@lem5109655 A x lt2 h1)). Qed.
Lemma lem5109658 {A : Type'} (lt2 : type1402 A) (x : A) : (term150 A lt2 x) = ((term150 A lt2 x) = True).
Proof. exact (@lem7 (term150 A lt2 x)). Qed.
Lemma lem5109676 {A : Type'} (x : A) (s : A -> Prop) : (term883 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem5109637 A x s) (@lem5109636 A s x)). Qed.
Lemma lem5109677 {A : Type'} (x : A) (s : A -> Prop) : (term883 A x s) = (@FINITE A s).
Proof. exact (@lem5109676 A x s). Qed.
Lemma lem5109678 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term885 A lt2 s) = (term886 A lt2 s).
Proof. exact (@lem5109677 A (term887 A s) (term888 A lt2 s)). Qed.
Lemma lem5109680 {A : Type'} (x : A) (lt2 : type1402 A) (h1 : term57 A lt2) : (term150 A lt2 x) = True.
Proof. exact (EQ_MP (@lem5109658 A lt2 x) (@lem5109657 A x lt2 h1)). Qed.
Lemma lem5109681 {A : Type'} (x : A) (lt2 : type1402 A) (h1 : term57 A lt2) : (term150 A lt2 x) = True.
Proof. exact (@lem5109680 A x lt2 h1). Qed.
Lemma lem5109682 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (h1 : term57 A lt2) : (term886 A lt2 s) = True.
Proof. exact (@lem5109681 A (term887 A s) lt2 h1). Qed.
Lemma lem5109683 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (h1 : term57 A lt2) : (term885 A lt2 s) = True.
Proof. exact (TRANS (@lem5109678 A lt2 s) (@lem5109682 A s lt2 h1)). Qed.
Lemma lem5109684 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5109685 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (h1 : term57 A lt2) : (term889 A lt2 s) = (and True).
Proof. exact (MK_COMB (@lem5109684) (@lem5109683 A s lt2 h1)). Qed.
Lemma lem5109692 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term890 A lt2 s) = (term890 A lt2 s).
Proof. exact (eq_refl (term890 A lt2 s)). Qed.
Lemma lem5109693 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (h1 : term57 A lt2) : (term891 A lt2 s) = (term892 A lt2 s).
Proof. exact (MK_COMB (@lem5109685 A s lt2 h1) (@lem5109692 A lt2 s)). Qed.
Lemma lem5109695 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5109696 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term892 A lt2 s) = (term890 A lt2 s).
Proof. exact (@lem5109695 (term890 A lt2 s)). Qed.
Lemma lem5109703 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (h1 : term57 A lt2) : (term891 A lt2 s) = (term890 A lt2 s).
Proof. exact (TRANS (@lem5109693 A s lt2 h1) (@lem5109696 A lt2 s)). Qed.
Lemma lem5109704 {A : Type'} (s : nat -> A) (lt2 : type1402 A) (h1 : term57 A lt2) : (term890 A lt2 s) = (term891 A lt2 s).
Proof. exact (SYM (@lem5109703 A s lt2 h1)). Qed.
Lemma lem5109706 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term21 A s t).
Proof. exact (EQ_MP (@lem5103172 A s t) (@lem5103171 A s t)). Qed.
Lemma lem5109707 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term21 A s t).
Proof. exact (@lem5109706 A s t). Qed.
Lemma lem5109708 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term890 A lt2 s) = (term893 A lt2 s).
Proof. exact (@lem5109707 A (@IMAGE nat A s (@UNIV nat)) (term894 A lt2 s)). Qed.
Lemma lem5109710 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term16 _87967 _87968 f s P) = (term17 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem5103166 _87967 _87968 s P f) (@lem5103165 _87967 _87968 P f s)). Qed.
Lemma lem5109711 {A : Type'} (s : nat -> Prop) (P : A -> Prop) (f : nat -> A) : (term895 A f s P) = (term896 A s P f).
Proof. exact (@lem5109710 A nat s P f). Qed.
Lemma lem5109712 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term897 A lt2 s) = (term898 A lt2 s).
Proof. exact (@lem5109711 A (@UNIV nat) (term899 A lt2 s) s). Qed.
Lemma lem5109713 {A : Type'} (x : A) (lt2 : type1402 A) (s : nat -> A) : (term900 A lt2 s x) = (term901 A x lt2 s).
Proof. exact (eq_refl (term900 A lt2 s x)). Qed.
Lemma lem5109714 {A : Type'} (x : A) (s : nat -> A) : (term902 A x s) = (term902 A x s).
Proof. exact (eq_refl (term902 A x s)). Qed.
Lemma lem5109715 {A : Type'} (x : A) (lt2 : type1402 A) (s : nat -> A) : (term903 A lt2 s x) = (term904 A x lt2 s).
Proof. exact (MK_COMB (@lem5109714 A x s) (@lem5109713 A x lt2 s)). Qed.
Lemma lem5109716 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term905 A lt2 s) = (term906 A lt2 s).
Proof. exact (fun_ext (fun x : A => @lem5109715 A x lt2 s)). Qed.
Lemma lem5109717 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5109718 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term897 A lt2 s) = (term893 A lt2 s).
Proof. exact (MK_COMB (@lem5109717 A) (@lem5109716 A lt2 s)). Qed.
Lemma lem5109719 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5109720 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term907 A lt2 s) = (term908 A lt2 s).
Proof. exact (MK_COMB (@lem5109719) (@lem5109718 A lt2 s)). Qed.
Lemma lem5109721 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) : (term909 A lt2 s x) = (term910 A x lt2 s).
Proof. exact (eq_refl (term909 A lt2 s x)). Qed.
Lemma lem5109722 (x : nat) : (term911 x) = (term911 x).
Proof. exact (eq_refl (term911 x)). Qed.
Lemma lem5109723 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) : (term912 A lt2 s x) = (term913 A x lt2 s).
Proof. exact (MK_COMB (@lem5109722 x) (@lem5109721 A x lt2 s)). Qed.
Lemma lem5109724 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term914 A lt2 s) = (term915 A lt2 s).
Proof. exact (fun_ext (fun x : nat => @lem5109723 A x lt2 s)). Qed.
Lemma lem5109725 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5109726 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term898 A lt2 s) = (term916 A lt2 s).
Proof. exact (MK_COMB (@lem5109725) (@lem5109724 A lt2 s)). Qed.
Lemma lem5109727 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : ((term897 A lt2 s) = (term898 A lt2 s)) = ((term893 A lt2 s) = (term916 A lt2 s)).
Proof. exact (MK_COMB (@lem5109720 A lt2 s) (@lem5109726 A lt2 s)). Qed.
Lemma lem5109728 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term893 A lt2 s) = (term916 A lt2 s).
Proof. exact (EQ_MP (@lem5109727 A lt2 s) (@lem5109712 A lt2 s)). Qed.
Lemma lem5109733 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term890 A lt2 s) = (term916 A lt2 s).
Proof. exact (TRANS (@lem5109708 A lt2 s) (@lem5109728 A lt2 s)). Qed.
Lemma lem5109737 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5103160 A x) (@lem5103159 A x)). Qed.
Lemma lem5109738 (x : nat) : (@IN nat x (@UNIV nat)) = True.
Proof. exact (@lem5109737 nat x). Qed.
Lemma lem5109739 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5109740 (x : nat) : (term911 x) = (imp True).
Proof. exact (MK_COMB (@lem5109739) (@lem5109738 x)). Qed.
Lemma lem5109742 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term10 A x y s) = (term11 A y x s).
Proof. exact (EQ_MP (@lem5103155 A y x s) (@lem5103154 A y x s)). Qed.
Lemma lem5109743 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term10 A x y s) = (term11 A y x s).
Proof. exact (@lem5109742 A y x s). Qed.
Lemma lem5109744 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) : (term910 A x lt2 s) = (term917 A x lt2 s).
Proof. exact (@lem5109743 A (term887 A s) (s x) (term888 A lt2 s)). Qed.
Lemma lem5109753 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) : (term913 A x lt2 s) = (term918 A x lt2 s).
Proof. exact (MK_COMB (@lem5109740 x) (@lem5109744 A x lt2 s)). Qed.
Lemma lem5109755 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5109756 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) : (term918 A x lt2 s) = (term917 A x lt2 s).
Proof. exact (@lem5109755 (term917 A x lt2 s)). Qed.
Lemma lem5109765 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) : (term913 A x lt2 s) = (term917 A x lt2 s).
Proof. exact (TRANS (@lem5109753 A x lt2 s) (@lem5109756 A x lt2 s)). Qed.
Lemma lem5109766 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term915 A lt2 s) = (term919 A lt2 s).
Proof. exact (fun_ext (fun x : nat => @lem5109765 A x lt2 s)). Qed.
Lemma lem5109767 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5109768 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term916 A lt2 s) = (term920 A lt2 s).
Proof. exact (MK_COMB (@lem5109767) (@lem5109766 A lt2 s)). Qed.
Lemma lem5109773 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term890 A lt2 s) = (term920 A lt2 s).
Proof. exact (TRANS (@lem5109733 A lt2 s) (@lem5109768 A lt2 s)). Qed.
Lemma lem5109774 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term920 A lt2 s) = (term890 A lt2 s).
Proof. exact (SYM (@lem5109773 A lt2 s)). Qed.
Lemma lem5109776 (P : nat -> Prop) : term921 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem5109777 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term922 A lt2 s.
Proof. exact (@lem5109776 (term919 A lt2 s)). Qed.
Lemma lem5109778 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term923 A lt2 s) = (term924 A lt2 s).
Proof. exact (eq_refl (term923 A lt2 s)). Qed.
Lemma lem5109779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5109780 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term925 A lt2 s) = (term926 A lt2 s).
Proof. exact (MK_COMB (@lem5109779) (@lem5109778 A lt2 s)). Qed.
Lemma lem5109781 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) : (term927 A lt2 s x) = (term917 A x lt2 s).
Proof. exact (eq_refl (term927 A lt2 s x)). Qed.
Lemma lem5109782 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5109783 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) : (term928 A lt2 s x) = (term929 A x lt2 s).
Proof. exact (MK_COMB (@lem5109782) (@lem5109781 A x lt2 s)). Qed.
Lemma lem5109784 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) : (term930 A lt2 s x) = (term931 A x lt2 s).
Proof. exact (eq_refl (term930 A lt2 s x)). Qed.
Lemma lem5109785 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) : (term932 A lt2 s x) = (term933 A x lt2 s).
Proof. exact (MK_COMB (@lem5109783 A x lt2 s) (@lem5109784 A x lt2 s)). Qed.
Lemma lem5109786 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term934 A lt2 s) = (term935 A lt2 s).
Proof. exact (fun_ext (fun x : nat => @lem5109785 A x lt2 s)). Qed.
Lemma lem5109787 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5109788 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term936 A lt2 s) = (term937 A lt2 s).
Proof. exact (MK_COMB (@lem5109787) (@lem5109786 A lt2 s)). Qed.
Lemma lem5109789 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term938 A lt2 s) = (term939 A lt2 s).
Proof. exact (MK_COMB (@lem5109780 A lt2 s) (@lem5109788 A lt2 s)). Qed.
Lemma lem5109790 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5109791 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term940 A lt2 s) = (term941 A lt2 s).
Proof. exact (MK_COMB (@lem5109790) (@lem5109789 A lt2 s)). Qed.
Lemma lem5109792 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) : (term927 A lt2 s x) = (term917 A x lt2 s).
Proof. exact (eq_refl (term927 A lt2 s x)). Qed.
Lemma lem5109793 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term942 A lt2 s) = (term919 A lt2 s).
Proof. exact (fun_ext (fun x : nat => @lem5109792 A x lt2 s)). Qed.
Lemma lem5109794 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5109795 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term943 A lt2 s) = (term920 A lt2 s).
Proof. exact (MK_COMB (@lem5109794) (@lem5109793 A lt2 s)). Qed.
Lemma lem5109796 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term922 A lt2 s) = (term944 A lt2 s).
Proof. exact (MK_COMB (@lem5109791 A lt2 s) (@lem5109795 A lt2 s)). Qed.
Lemma lem5109797 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term944 A lt2 s.
Proof. exact (EQ_MP (@lem5109796 A lt2 s) (@lem5109777 A lt2 s)). Qed.
Lemma lem5109798 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term917 A x lt2 s) : term917 A x lt2 s.
Proof. exact (h1). Qed.
Lemma lem5109802 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5109803 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem5109802 A x). Qed.
Lemma lem5109804 {A : Type'} (s : nat -> A) : ((term887 A s) = (term887 A s)) = True.
Proof. exact (@lem5109803 A (term887 A s)). Qed.
Lemma lem5109805 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5109806 {A : Type'} (s : nat -> A) : (term945 A s) = (or True).
Proof. exact (MK_COMB (@lem5109805) (@lem5109804 A s)). Qed.
Lemma lem5109808 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5103139 _83095 p x) (@lem5103138 _83095 p x)). Qed.
Lemma lem5109809 {A : Type'} (p : A -> Prop) (x : A) : (term4 A x p) = (p x).
Proof. exact (@lem5109808 A p x). Qed.
Lemma lem5109810 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term946 A lt2 s) = (term947 A lt2 s).
Proof. exact (@lem5109809 A (term948 A lt2 s) (term887 A s)). Qed.
Lemma lem5109811 {A : Type'} (lt2 : type1402 A) (y : A) (s : nat -> A) : (term949 A lt2 s y) = (term950 A lt2 y s).
Proof. exact (eq_refl (term949 A lt2 s y)). Qed.
Lemma lem5109812 {A : Type'} (GEN_PVAR_226 : A) : (@SETSPEC A GEN_PVAR_226) = (@SETSPEC A GEN_PVAR_226).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_226)). Qed.
Lemma lem5109813 {A : Type'} (GEN_PVAR_226 : A) (lt2 : type1402 A) (y : A) (s : nat -> A) : (term951 A GEN_PVAR_226 lt2 s y) = (term952 A GEN_PVAR_226 lt2 y s).
Proof. exact (MK_COMB (@lem5109812 A GEN_PVAR_226) (@lem5109811 A lt2 y s)). Qed.
Lemma lem5109814 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5109815 {A : Type'} (GEN_PVAR_226 : A) (lt2 : type1402 A) (s : nat -> A) (y : A) : (term953 A GEN_PVAR_226 lt2 s y) = (term954 A GEN_PVAR_226 lt2 s y).
Proof. exact (MK_COMB (@lem5109813 A GEN_PVAR_226 lt2 y s) (@lem5109814 A y)). Qed.
Lemma lem5109816 {A : Type'} (GEN_PVAR_226 : A) (lt2 : type1402 A) (s : nat -> A) : (term955 A GEN_PVAR_226 lt2 s) = (term956 A GEN_PVAR_226 lt2 s).
Proof. exact (fun_ext (fun y : A => @lem5109815 A GEN_PVAR_226 lt2 s y)). Qed.
Lemma lem5109817 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5109818 {A : Type'} (GEN_PVAR_226 : A) (lt2 : type1402 A) (s : nat -> A) : (term957 A GEN_PVAR_226 lt2 s) = (term958 A GEN_PVAR_226 lt2 s).
Proof. exact (MK_COMB (@lem5109817 A) (@lem5109816 A GEN_PVAR_226 lt2 s)). Qed.
Lemma lem5109819 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term959 A lt2 s) = (term960 A lt2 s).
Proof. exact (fun_ext (fun GEN_PVAR_226 : A => @lem5109818 A GEN_PVAR_226 lt2 s)). Qed.
Lemma lem5109820 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5109821 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term961 A lt2 s) = (term888 A lt2 s).
Proof. exact (MK_COMB (@lem5109820 A) (@lem5109819 A lt2 s)). Qed.
Lemma lem5109822 {A : Type'} (s : nat -> A) : (term962 A s) = (term962 A s).
Proof. exact (eq_refl (term962 A s)). Qed.
Lemma lem5109823 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term946 A lt2 s) = (term963 A lt2 s).
Proof. exact (MK_COMB (@lem5109822 A s) (@lem5109821 A lt2 s)). Qed.
Lemma lem5109824 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5109825 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term964 A lt2 s) = (term965 A lt2 s).
Proof. exact (MK_COMB (@lem5109824) (@lem5109823 A lt2 s)). Qed.
Lemma lem5109826 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term947 A lt2 s) = (term966 A lt2 s).
Proof. exact (eq_refl (term947 A lt2 s)). Qed.
Lemma lem5109827 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : ((term946 A lt2 s) = (term947 A lt2 s)) = ((term963 A lt2 s) = (term966 A lt2 s)).
Proof. exact (MK_COMB (@lem5109825 A lt2 s) (@lem5109826 A lt2 s)). Qed.
Lemma lem5109828 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term963 A lt2 s) = (term966 A lt2 s).
Proof. exact (EQ_MP (@lem5109827 A lt2 s) (@lem5109810 A lt2 s)). Qed.
Lemma lem5109829 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term924 A lt2 s) = (term967 A lt2 s).
Proof. exact (MK_COMB (@lem5109806 A s) (@lem5109828 A lt2 s)). Qed.
Lemma lem5109831 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem5109832 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term967 A lt2 s) = True.
Proof. exact (@lem5109831 (term966 A lt2 s)). Qed.
Lemma lem5109833 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term924 A lt2 s) = True.
Proof. exact (TRANS (@lem5109829 A lt2 s) (@lem5109832 A lt2 s)). Qed.
Lemma lem5109834 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : True = (term924 A lt2 s).
Proof. exact (SYM (@lem5109833 A lt2 s)). Qed.
Lemma lem5109835 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : term924 A lt2 s.
Proof. exact (EQ_MP (@lem5109834 A lt2 s) (@lem0)). Qed.
Lemma lem5109841 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term4 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5103139 _83095 p x) (@lem5103138 _83095 p x)). Qed.
Lemma lem5109842 {A : Type'} (p : A -> Prop) (x : A) : (term4 A x p) = (p x).
Proof. exact (@lem5109841 A p x). Qed.
Lemma lem5109843 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term968 A x lt2 s) = (term969 A lt2 s x).
Proof. exact (@lem5109842 A (term948 A lt2 s) (term563 A s x)). Qed.
Lemma lem5109844 {A : Type'} (lt2 : type1402 A) (y : A) (s : nat -> A) : (term949 A lt2 s y) = (term950 A lt2 y s).
Proof. exact (eq_refl (term949 A lt2 s y)). Qed.
Lemma lem5109845 {A : Type'} (GEN_PVAR_226 : A) : (@SETSPEC A GEN_PVAR_226) = (@SETSPEC A GEN_PVAR_226).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_226)). Qed.
Lemma lem5109846 {A : Type'} (GEN_PVAR_226 : A) (lt2 : type1402 A) (y : A) (s : nat -> A) : (term951 A GEN_PVAR_226 lt2 s y) = (term952 A GEN_PVAR_226 lt2 y s).
Proof. exact (MK_COMB (@lem5109845 A GEN_PVAR_226) (@lem5109844 A lt2 y s)). Qed.
Lemma lem5109847 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5109848 {A : Type'} (GEN_PVAR_226 : A) (lt2 : type1402 A) (s : nat -> A) (y : A) : (term953 A GEN_PVAR_226 lt2 s y) = (term954 A GEN_PVAR_226 lt2 s y).
Proof. exact (MK_COMB (@lem5109846 A GEN_PVAR_226 lt2 y s) (@lem5109847 A y)). Qed.
Lemma lem5109849 {A : Type'} (GEN_PVAR_226 : A) (lt2 : type1402 A) (s : nat -> A) : (term955 A GEN_PVAR_226 lt2 s) = (term956 A GEN_PVAR_226 lt2 s).
Proof. exact (fun_ext (fun y : A => @lem5109848 A GEN_PVAR_226 lt2 s y)). Qed.
Lemma lem5109850 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5109851 {A : Type'} (GEN_PVAR_226 : A) (lt2 : type1402 A) (s : nat -> A) : (term957 A GEN_PVAR_226 lt2 s) = (term958 A GEN_PVAR_226 lt2 s).
Proof. exact (MK_COMB (@lem5109850 A) (@lem5109849 A GEN_PVAR_226 lt2 s)). Qed.
Lemma lem5109852 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term959 A lt2 s) = (term960 A lt2 s).
Proof. exact (fun_ext (fun GEN_PVAR_226 : A => @lem5109851 A GEN_PVAR_226 lt2 s)). Qed.
Lemma lem5109853 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5109854 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term961 A lt2 s) = (term888 A lt2 s).
Proof. exact (MK_COMB (@lem5109853 A) (@lem5109852 A lt2 s)). Qed.
Lemma lem5109855 {A : Type'} (s : nat -> A) (x : nat) : (term970 A s x) = (term970 A s x).
Proof. exact (eq_refl (term970 A s x)). Qed.
Lemma lem5109856 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) : (term968 A x lt2 s) = (term971 A x lt2 s).
Proof. exact (MK_COMB (@lem5109855 A s x) (@lem5109854 A lt2 s)). Qed.
Lemma lem5109857 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5109858 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) : (term972 A x lt2 s) = (term973 A x lt2 s).
Proof. exact (MK_COMB (@lem5109857) (@lem5109856 A x lt2 s)). Qed.
Lemma lem5109859 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term969 A lt2 s x) = (term974 A lt2 x s).
Proof. exact (eq_refl (term969 A lt2 s x)). Qed.
Lemma lem5109860 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : ((term968 A x lt2 s) = (term969 A lt2 s x)) = ((term971 A x lt2 s) = (term974 A lt2 x s)).
Proof. exact (MK_COMB (@lem5109858 A x lt2 s) (@lem5109859 A lt2 x s)). Qed.
Lemma lem5109861 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term971 A x lt2 s) = (term974 A lt2 x s).
Proof. exact (EQ_MP (@lem5109860 A lt2 x s) (@lem5109843 A lt2 s x)). Qed.
Lemma lem5109862 {A : Type'} (x : nat) (s : nat -> A) : (term975 A x s) = (term975 A x s).
Proof. exact (eq_refl (term975 A x s)). Qed.
Lemma lem5109863 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term931 A x lt2 s) = (term976 A lt2 x s).
Proof. exact (MK_COMB (@lem5109862 A x s) (@lem5109861 A lt2 x s)). Qed.
Lemma lem5109866 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) : (term976 A lt2 x s) = (term931 A x lt2 s).
Proof. exact (SYM (@lem5109863 A lt2 x s)). Qed.
Lemma lem5109868 (p : Prop) : p = (term113 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5109869 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term976 A lt2 x s) = (term977 A lt2 x s).
Proof. exact (@lem5109868 (term976 A lt2 x s)). Qed.
Lemma lem5109870 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term977 A lt2 x s) = (term976 A lt2 x s).
Proof. exact (SYM (@lem5109869 A lt2 x s)). Qed.
Lemma lem5109871 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term978 A lt2 x s) : term978 A lt2 x s.
Proof. exact (h1). Qed.
Lemma lem5109874 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term979 A lt2 x s) : term979 A lt2 x s.
Proof. exact (h1). Qed.
Lemma lem5109875 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : term980 A lt2 x s.
Proof. exact (fun h0 : term979 A lt2 x s => @lem5109874 A lt2 x s h0). Qed.
Lemma lem5109876 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term980 A lt2 x s) : term980 A lt2 x s.
Proof. exact (h1). Qed.
Lemma lem5109877 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term979 A lt2 x s) : term979 A lt2 x s.
Proof. exact (h1). Qed.
Lemma lem5109878 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term979 A lt2 x s) (h2 : term980 A lt2 x s) : term979 A lt2 x s.
Proof. exact (@lem5109876 A lt2 x s h2 (@lem5109877 A lt2 x s h1)). Qed.
Lemma lem5109879 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term979 A lt2 x s) : term981 A lt2 x s.
Proof. exact (fun h0 : term980 A lt2 x s => @lem5109878 A lt2 x s h1 h0). Qed.
Lemma lem5109880 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term980 A lt2 x s) : term980 A lt2 x s.
Proof. exact (h1). Qed.
Lemma lem5109881 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term979 A lt2 x s) (h2 : term980 A lt2 x s) : term979 A lt2 x s.
Proof. exact (@lem5109879 A lt2 x s h1 (@lem5109880 A lt2 x s h2)). Qed.
Lemma lem5109882 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term980 A lt2 x s) : term980 A lt2 x s.
Proof. exact (fun h0 : term979 A lt2 x s => @lem5109881 A lt2 x s h0 h1). Qed.
Lemma lem5109883 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : term982 A lt2 x s.
Proof. exact (fun h0 : term980 A lt2 x s => @lem5109882 A lt2 x s h0). Qed.
Lemma lem5109886 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : term980 A lt2 x s.
Proof. exact (@lem5109883 A lt2 x s (@lem5109875 A lt2 x s)). Qed.
Lemma lem5109887 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : term980 A lt2 x s.
Proof. exact (@lem5109886 A lt2 x s). Qed.
Lemma lem5109965 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5109966 : term983 = term984.
Proof. exact (@lem5109965 term985). Qed.
Lemma lem5109971 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term986 A lt2 x s) = (term986 A lt2 x s).
Proof. exact (eq_refl (term986 A lt2 x s)). Qed.
Lemma lem5109972 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term987 A lt2 x s) = (term988 A lt2 x s).
Proof. exact (MK_COMB (@lem5109971 A lt2 x s) (@lem5109966)). Qed.
Lemma lem5109975 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) : (term929 A x lt2 s) = (term929 A x lt2 s).
Proof. exact (eq_refl (term929 A x lt2 s)). Qed.
Lemma lem5109976 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term989 A lt2 x s) = (term990 A lt2 x s).
Proof. exact (MK_COMB (@lem5109975 A x lt2 s) (@lem5109972 A lt2 x s)). Qed.
Lemma lem5109979 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term640 A lt2 s) = (term640 A lt2 s).
Proof. exact (eq_refl (term640 A lt2 s)). Qed.
Lemma lem5109980 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term991 A lt2 x s) = (term992 A lt2 x s).
Proof. exact (MK_COMB (@lem5109979 A lt2 s) (@lem5109976 A lt2 x s)). Qed.
Lemma lem5109983 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term122 A lt2 s) = (term122 A lt2 s).
Proof. exact (eq_refl (term122 A lt2 s)). Qed.
Lemma lem5109984 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term993 A lt2 x s) = (term994 A lt2 x s).
Proof. exact (MK_COMB (@lem5109983 A lt2 s) (@lem5109980 A lt2 x s)). Qed.
Lemma lem5109987 {A : Type'} (lt2 : type1402 A) : (term125 A lt2) = (term125 A lt2).
Proof. exact (eq_refl (term125 A lt2)). Qed.
Lemma lem5109988 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term995 A lt2 x s) = (term996 A lt2 x s).
Proof. exact (MK_COMB (@lem5109987 A lt2) (@lem5109984 A lt2 x s)). Qed.
Lemma lem5109991 {A : Type'} (lt2 : type1402 A) : (term128 A lt2) = (term128 A lt2).
Proof. exact (eq_refl (term128 A lt2)). Qed.
Lemma lem5109992 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term997 A lt2 x s) = (term998 A lt2 x s).
Proof. exact (MK_COMB (@lem5109991 A lt2) (@lem5109988 A lt2 x s)). Qed.
Lemma lem5109995 {A : Type'} (lt2 : type1402 A) : (term131 A lt2) = (term131 A lt2).
Proof. exact (eq_refl (term131 A lt2)). Qed.
Lemma lem5109996 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term979 A lt2 x s) = (term999 A lt2 x s).
Proof. exact (MK_COMB (@lem5109995 A lt2) (@lem5109992 A lt2 x s)). Qed.
Lemma lem5109999 {A : Type'} (x : nat) (s : nat -> A) : (term1000 A x s) = (term1001 A x s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5109996 A lt2 x s)). Qed.
Lemma lem5110000 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5110001 {A : Type'} (x : nat) (s : nat -> A) : (term1002 A x s) = (term1003 A x s).
Proof. exact (MK_COMB (@lem5110000 A) (@lem5109999 A x s)). Qed.
Lemma lem5110006 {A : Type'} (s : nat -> A) : (term1004 A s) = (term1005 A s).
Proof. exact (fun_ext (fun x : nat => @lem5110001 A x s)). Qed.
Lemma lem5110007 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5110008 {A : Type'} (s : nat -> A) : (term1006 A s) = (term1007 A s).
Proof. exact (MK_COMB (@lem5110007) (@lem5110006 A s)). Qed.
Lemma lem5110013 {A : Type'} : (term1008 A) = (term1009 A).
Proof. exact (fun_ext (fun s : nat -> A => @lem5110008 A s)). Qed.
Lemma lem5110014 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5110021 {A : Type'} : (term1010 A) = (term1011 A).
Proof. exact (MK_COMB (@lem5110014 A) (@lem5110013 A)). Qed.
Lemma lem5110022 {A : Type'} (_66640 : type418 A) (h1 : _66640 = (term141 A)) : _66640 = (term141 A).
Proof. exact (h1). Qed.
Lemma lem5110023 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem5110024 {A : Type'} (lt2 : type1402 A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (_66640 lt2) = (term142 A lt2).
Proof. exact (MK_COMB (@lem5110022 A _66640 h1) (@lem5110023 A lt2)). Qed.
Lemma lem5110025 {A : Type'} (lt2 : type1402 A) : (term142 A lt2) = (term143 A lt2).
Proof. exact (eq_refl (term142 A lt2)). Qed.
Lemma lem5110026 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term144 A _66640 lt2) = (term144 A _66640 lt2).
Proof. exact (eq_refl (term144 A _66640 lt2)). Qed.
Lemma lem5110027 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : ((_66640 lt2) = (term142 A lt2)) = ((_66640 lt2) = (term143 A lt2)).
Proof. exact (MK_COMB (@lem5110026 A _66640 lt2) (@lem5110025 A lt2)). Qed.
Lemma lem5110028 {A : Type'} (lt2 : type1402 A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (_66640 lt2) = (term143 A lt2).
Proof. exact (EQ_MP (@lem5110027 A _66640 lt2) (@lem5110024 A lt2 _66640 h1)). Qed.
Lemma lem5110029 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5110030 {A : Type'} (lt2 : type1402 A) (x : A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (_66640 lt2 x) = (term145 A lt2 x).
Proof. exact (MK_COMB (@lem5110028 A lt2 _66640 h1) (@lem5110029 A x)). Qed.
Lemma lem5110031 {A : Type'} (lt2 : type1402 A) (x : A) : (term145 A lt2 x) = (term146 A lt2 x).
Proof. exact (eq_refl (term145 A lt2 x)). Qed.
Lemma lem5110032 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term147 A _66640 lt2 x) = (term147 A _66640 lt2 x).
Proof. exact (eq_refl (term147 A _66640 lt2 x)). Qed.
Lemma lem5110033 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : ((_66640 lt2 x) = (term145 A lt2 x)) = ((_66640 lt2 x) = (term146 A lt2 x)).
Proof. exact (MK_COMB (@lem5110032 A _66640 lt2 x) (@lem5110031 A lt2 x)). Qed.
Lemma lem5110034 {A : Type'} (lt2 : type1402 A) (x : A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (_66640 lt2 x) = (term146 A lt2 x).
Proof. exact (EQ_MP (@lem5110033 A _66640 lt2 x) (@lem5110030 A lt2 x _66640 h1)). Qed.
Lemma lem5110044 (n : nat) : (term1012 n) = (term1012 n).
Proof. exact (eq_refl (term1012 n)). Qed.
Lemma lem5110045 : term1013 = term1013.
Proof. exact (fun_ext (fun n : nat => @lem5110044 n)). Qed.
Lemma lem5110046 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5110047 : term985 = term985.
Proof. exact (MK_COMB (@lem5110046) (@lem5110045)). Qed.
Lemma lem5110048 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5110049 : term984 = term984.
Proof. exact (MK_COMB (@lem5110048) (@lem5110047)). Qed.
Lemma lem5110082 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term986 A lt2 x s) = (term986 A lt2 x s).
Proof. exact (eq_refl (term986 A lt2 x s)). Qed.
Lemma lem5110083 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term988 A lt2 x s) = (term988 A lt2 x s).
Proof. exact (MK_COMB (@lem5110082 A lt2 x s) (@lem5110049)). Qed.
Lemma lem5110085 {A : Type'} (lt2 : type1402 A) (x : A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term146 A lt2 x) = (_66640 lt2 x).
Proof. exact (SYM (@lem5110034 A lt2 x _66640 h1)). Qed.
Lemma lem5110086 {A : Type'} (lt2 : type1402 A) (x : A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term146 A lt2 x) = (_66640 lt2 x).
Proof. exact (@lem5110085 A lt2 x _66640 h1). Qed.
Lemma lem5110087 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term960 A lt2 s) = (term1014 A _66640 lt2 s).
Proof. exact (@lem5110086 A lt2 (term887 A s) _66640 h1). Qed.
Lemma lem5110088 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5110089 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term888 A lt2 s) = (term1015 A _66640 lt2 s).
Proof. exact (MK_COMB (@lem5110088 A) (@lem5110087 A lt2 s _66640 h1)). Qed.
Lemma lem5110094 {A : Type'} (s : nat -> A) (x : nat) : (term1016 A s x) = (term1016 A s x).
Proof. exact (eq_refl (term1016 A s x)). Qed.
Lemma lem5110095 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term1017 A x lt2 s) = (term1018 A x _66640 lt2 s).
Proof. exact (MK_COMB (@lem5110094 A s x) (@lem5110089 A lt2 s _66640 h1)). Qed.
Lemma lem5110108 {A : Type'} (x : nat) (s : nat -> A) : (term1019 A x s) = (term1019 A x s).
Proof. exact (eq_refl (term1019 A x s)). Qed.
Lemma lem5110109 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term917 A x lt2 s) = (term1020 A x _66640 lt2 s).
Proof. exact (MK_COMB (@lem5110108 A x s) (@lem5110095 A x lt2 s _66640 h1)). Qed.
Lemma lem5110110 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5110111 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term929 A x lt2 s) = (term1021 A x _66640 lt2 s).
Proof. exact (MK_COMB (@lem5110110) (@lem5110109 A x lt2 s _66640 h1)). Qed.
Lemma lem5110112 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term990 A lt2 x s) = (term1022 A _66640 lt2 x s).
Proof. exact (MK_COMB (@lem5110111 A x lt2 s _66640 h1) (@lem5110083 A lt2 x s)). Qed.
Lemma lem5110129 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term104 A lt2 n s m) = (term104 A lt2 n s m).
Proof. exact (eq_refl (term104 A lt2 n s m)). Qed.
Lemma lem5110130 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term106 A lt2 s m) = (term106 A lt2 s m).
Proof. exact (fun_ext (fun n : nat => @lem5110129 A lt2 n s m)). Qed.
Lemma lem5110131 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5110132 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term108 A lt2 s m) = (term108 A lt2 s m).
Proof. exact (MK_COMB (@lem5110131) (@lem5110130 A lt2 s m)). Qed.
Lemma lem5110133 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term110 A lt2 s) = (term110 A lt2 s).
Proof. exact (fun_ext (fun m : nat => @lem5110132 A lt2 s m)). Qed.
Lemma lem5110134 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5110135 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term62 A lt2 s) = (term62 A lt2 s).
Proof. exact (MK_COMB (@lem5110134) (@lem5110133 A lt2 s)). Qed.
Lemma lem5110136 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5110137 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term640 A lt2 s) = (term640 A lt2 s).
Proof. exact (MK_COMB (@lem5110136) (@lem5110135 A lt2 s)). Qed.
Lemma lem5110138 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term992 A lt2 x s) = (term1023 A _66640 lt2 x s).
Proof. exact (MK_COMB (@lem5110137 A lt2 s) (@lem5110112 A lt2 x s _66640 h1)). Qed.
Lemma lem5110149 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term94 A lt2 s n) = (term94 A lt2 s n).
Proof. exact (eq_refl (term94 A lt2 s n)). Qed.
Lemma lem5110150 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term96 A lt2 s) = (term96 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5110149 A lt2 s n)). Qed.
Lemma lem5110151 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5110152 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term61 A lt2 s) = (term61 A lt2 s).
Proof. exact (MK_COMB (@lem5110151) (@lem5110150 A lt2 s)). Qed.
Lemma lem5110153 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5110154 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term122 A lt2 s) = (term122 A lt2 s).
Proof. exact (MK_COMB (@lem5110153) (@lem5110152 A lt2 s)). Qed.
Lemma lem5110155 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term994 A lt2 x s) = (term1024 A _66640 lt2 x s).
Proof. exact (MK_COMB (@lem5110154 A lt2 s) (@lem5110138 A lt2 x s _66640 h1)). Qed.
Lemma lem5110157 {A : Type'} (lt2 : type1402 A) (x : A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term146 A lt2 x) = (_66640 lt2 x).
Proof. exact (SYM (@lem5110034 A lt2 x _66640 h1)). Qed.
Lemma lem5110158 {A : Type'} (lt2 : type1402 A) (x : A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term146 A lt2 x) = (_66640 lt2 x).
Proof. exact (@lem5110157 A lt2 x _66640 h1). Qed.
Lemma lem5110159 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5110160 {A : Type'} (lt2 : type1402 A) (x : A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term148 A lt2 x) = (term149 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5110159 A) (@lem5110158 A lt2 x _66640 h1)). Qed.
Lemma lem5110161 {A : Type'} : (@FINITE A) = (@FINITE A).
Proof. exact (eq_refl (@FINITE A)). Qed.
Lemma lem5110162 {A : Type'} (lt2 : type1402 A) (x : A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term150 A lt2 x) = (term151 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5110161 A) (@lem5110160 A lt2 x _66640 h1)). Qed.
Lemma lem5110163 {A : Type'} (lt2 : type1402 A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term152 A lt2) = (term153 A _66640 lt2).
Proof. exact (fun_ext (fun x : A => @lem5110162 A lt2 x _66640 h1)). Qed.
Lemma lem5110164 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110165 {A : Type'} (lt2 : type1402 A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term57 A lt2) = (term154 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110164 A) (@lem5110163 A lt2 _66640 h1)). Qed.
Lemma lem5110166 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5110167 {A : Type'} (lt2 : type1402 A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term125 A lt2) = (term155 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110166) (@lem5110165 A lt2 _66640 h1)). Qed.
Lemma lem5110168 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term996 A lt2 x s) = (term1025 A _66640 lt2 x s).
Proof. exact (MK_COMB (@lem5110167 A lt2 _66640 h1) (@lem5110155 A lt2 x s _66640 h1)). Qed.
Lemma lem5110189 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term157 A y lt2 x z) = (term157 A y lt2 x z).
Proof. exact (eq_refl (term157 A y lt2 x z)). Qed.
Lemma lem5110190 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term158 A y lt2 x) = (term158 A y lt2 x).
Proof. exact (fun_ext (fun z : A => @lem5110189 A y lt2 x z)). Qed.
Lemma lem5110191 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110192 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term159 A y lt2 x) = (term159 A y lt2 x).
Proof. exact (MK_COMB (@lem5110191 A) (@lem5110190 A y lt2 x)). Qed.
Lemma lem5110193 {A : Type'} (lt2 : type1402 A) (x : A) : (term160 A lt2 x) = (term160 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5110192 A y lt2 x)). Qed.
Lemma lem5110194 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110195 {A : Type'} (lt2 : type1402 A) (x : A) : (term161 A lt2 x) = (term161 A lt2 x).
Proof. exact (MK_COMB (@lem5110194 A) (@lem5110193 A lt2 x)). Qed.
Lemma lem5110196 {A : Type'} (lt2 : type1402 A) : (term162 A lt2) = (term162 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5110195 A lt2 x)). Qed.
Lemma lem5110197 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110198 {A : Type'} (lt2 : type1402 A) : (term58 A lt2) = (term58 A lt2).
Proof. exact (MK_COMB (@lem5110197 A) (@lem5110196 A lt2)). Qed.
Lemma lem5110199 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5110200 {A : Type'} (lt2 : type1402 A) : (term128 A lt2) = (term128 A lt2).
Proof. exact (MK_COMB (@lem5110199) (@lem5110198 A lt2)). Qed.
Lemma lem5110201 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term998 A lt2 x s) = (term1026 A _66640 lt2 x s).
Proof. exact (MK_COMB (@lem5110200 A lt2) (@lem5110168 A lt2 x s _66640 h1)). Qed.
Lemma lem5110208 {A : Type'} (lt2 : type1402 A) (x : A) : (term164 A lt2 x) = (term164 A lt2 x).
Proof. exact (eq_refl (term164 A lt2 x)). Qed.
Lemma lem5110209 {A : Type'} (lt2 : type1402 A) : (term165 A lt2) = (term165 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5110208 A lt2 x)). Qed.
Lemma lem5110210 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110211 {A : Type'} (lt2 : type1402 A) : (term56 A lt2) = (term56 A lt2).
Proof. exact (MK_COMB (@lem5110210 A) (@lem5110209 A lt2)). Qed.
Lemma lem5110212 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5110213 {A : Type'} (lt2 : type1402 A) : (term131 A lt2) = (term131 A lt2).
Proof. exact (MK_COMB (@lem5110212) (@lem5110211 A lt2)). Qed.
Lemma lem5110214 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term999 A lt2 x s) = (term1027 A _66640 lt2 x s).
Proof. exact (MK_COMB (@lem5110213 A lt2) (@lem5110201 A lt2 x s _66640 h1)). Qed.
Lemma lem5110215 {A : Type'} (x : nat) (s : nat -> A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term1001 A x s) = (term1028 A _66640 x s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5110214 A lt2 x s _66640 h1)). Qed.
Lemma lem5110216 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5110217 {A : Type'} (x : nat) (s : nat -> A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term1003 A x s) = (term1029 A _66640 x s).
Proof. exact (MK_COMB (@lem5110216 A) (@lem5110215 A x s _66640 h1)). Qed.
Lemma lem5110218 {A : Type'} (s : nat -> A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term1005 A s) = (term1030 A _66640 s).
Proof. exact (fun_ext (fun x : nat => @lem5110217 A x s _66640 h1)). Qed.
Lemma lem5110219 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5110220 {A : Type'} (s : nat -> A) (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term1007 A s) = (term1031 A _66640 s).
Proof. exact (MK_COMB (@lem5110219) (@lem5110218 A s _66640 h1)). Qed.
Lemma lem5110221 {A : Type'} (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term1009 A) = (term1032 A _66640).
Proof. exact (fun_ext (fun s : nat -> A => @lem5110220 A s _66640 h1)). Qed.
Lemma lem5110222 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5110223 {A : Type'} (_66640 : type418 A) (h1 : _66640 = (term141 A)) : (term1011 A) = (term1033 A _66640).
Proof. exact (MK_COMB (@lem5110222 A) (@lem5110221 A _66640 h1)). Qed.
Lemma lem5110224 {A : Type'} (_66640 : type418 A) : term1034 A _66640.
Proof. exact (fun h0 : _66640 = (term141 A) => @lem5110223 A _66640 h0). Qed.
Lemma lem5110225 {A : Type'} : term1035 A.
Proof. exact (fun _66640 : type418 A => @lem5110224 A _66640). Qed.
Lemma lem5110227 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term173 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem5110228 {A : Type'} (P : Prop) (c : type418 A) (Q : type84 A) : term174 A P c Q.
Proof. exact (@lem5110227 (type418 A) P c Q). Qed.
Lemma lem5110229 {A : Type'} : term1036 A.
Proof. exact (@lem5110228 A (term1011 A) (term141 A) (term1037 A)). Qed.
Lemma lem5110230 {A : Type'} (_66640 : type418 A) : (term1038 A _66640) = (term1033 A _66640).
Proof. exact (eq_refl (term1038 A _66640)). Qed.
Lemma lem5110231 {A : Type'} : (term1039 A) = (term1039 A).
Proof. exact (eq_refl (term1039 A)). Qed.
Lemma lem5110232 {A : Type'} (_66640 : type418 A) : ((term1011 A) = (term1038 A _66640)) = ((term1011 A) = (term1033 A _66640)).
Proof. exact (MK_COMB (@lem5110231 A) (@lem5110230 A _66640)). Qed.
Lemma lem5110233 {A : Type'} (_66640 : type418 A) : (term179 A _66640) = (term179 A _66640).
Proof. exact (eq_refl (term179 A _66640)). Qed.
Lemma lem5110234 {A : Type'} (_66640 : type418 A) : (term1040 A _66640) = (term1034 A _66640).
Proof. exact (MK_COMB (@lem5110233 A _66640) (@lem5110232 A _66640)). Qed.
Lemma lem5110235 {A : Type'} : (term1041 A) = (term1042 A).
Proof. exact (fun_ext (fun _66640 : type418 A => @lem5110234 A _66640)). Qed.
Lemma lem5110236 {A : Type'} : (@all ((A -> A -> Prop) -> A -> A -> Prop)) = (@all ((A -> A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem5110237 {A : Type'} : (term1043 A) = (term1035 A).
Proof. exact (MK_COMB (@lem5110236 A) (@lem5110235 A)). Qed.
Lemma lem5110238 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5110239 {A : Type'} : (term1044 A) = (term1045 A).
Proof. exact (MK_COMB (@lem5110238) (@lem5110237 A)). Qed.
Lemma lem5110240 {A : Type'} (_66640 : type418 A) : (term1038 A _66640) = (term1033 A _66640).
Proof. exact (eq_refl (term1038 A _66640)). Qed.
Lemma lem5110241 {A : Type'} (_66640 : type418 A) : (term179 A _66640) = (term179 A _66640).
Proof. exact (eq_refl (term179 A _66640)). Qed.
Lemma lem5110242 {A : Type'} (_66640 : type418 A) : (term1046 A _66640) = (term1047 A _66640).
Proof. exact (MK_COMB (@lem5110241 A _66640) (@lem5110240 A _66640)). Qed.
Lemma lem5110243 {A : Type'} : (term1048 A) = (term1049 A).
Proof. exact (fun_ext (fun _66640 : type418 A => @lem5110242 A _66640)). Qed.
Lemma lem5110244 {A : Type'} : (@all ((A -> A -> Prop) -> A -> A -> Prop)) = (@all ((A -> A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem5110245 {A : Type'} : (term1050 A) = (term1051 A).
Proof. exact (MK_COMB (@lem5110244 A) (@lem5110243 A)). Qed.
Lemma lem5110246 {A : Type'} : (term1039 A) = (term1039 A).
Proof. exact (eq_refl (term1039 A)). Qed.
Lemma lem5110247 {A : Type'} : ((term1011 A) = (term1050 A)) = ((term1011 A) = (term1051 A)).
Proof. exact (MK_COMB (@lem5110246 A) (@lem5110245 A)). Qed.
Lemma lem5110248 {A : Type'} : (term1036 A) = (term1052 A).
Proof. exact (MK_COMB (@lem5110239 A) (@lem5110247 A)). Qed.
Lemma lem5110249 {A : Type'} : term1052 A.
Proof. exact (EQ_MP (@lem5110248 A) (@lem5110229 A)). Qed.
Lemma lem5110250 {A : Type'} : (term1011 A) = (term1051 A).
Proof. exact (@lem5110249 A (@lem5110225 A)). Qed.
Lemma lem5110252 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term193 _3571 _3575 t)) = (term194 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5110253 {A : Type'} (s : type418 A) (t : type418 A) : (s = (term195 A t)) = (term196 A s t).
Proof. exact (@lem5110252 (type1402 A) (type1402 A) s t). Qed.
Lemma lem5110254 {A : Type'} (_66640 : type418 A) : (_66640 = (term197 A)) = (term198 A _66640).
Proof. exact (@lem5110253 A _66640 (term141 A)). Qed.
Lemma lem5110255 {A : Type'} (lt2 : type1402 A) : (term142 A lt2) = (term143 A lt2).
Proof. exact (eq_refl (term142 A lt2)). Qed.
Lemma lem5110256 {A : Type'} : (term197 A) = (term141 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5110255 A lt2)). Qed.
Lemma lem5110257 {A : Type'} (_66640 : type418 A) : (@eq ((A -> A -> Prop) -> A -> A -> Prop) _66640) = (@eq ((A -> A -> Prop) -> A -> A -> Prop) _66640).
Proof. exact (eq_refl (@eq ((A -> A -> Prop) -> A -> A -> Prop) _66640)). Qed.
Lemma lem5110258 {A : Type'} (_66640 : type418 A) : (_66640 = (term197 A)) = (_66640 = (term141 A)).
Proof. exact (MK_COMB (@lem5110257 A _66640) (@lem5110256 A)). Qed.
Lemma lem5110259 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5110260 {A : Type'} (_66640 : type418 A) : (term199 A _66640) = (term200 A _66640).
Proof. exact (MK_COMB (@lem5110259) (@lem5110258 A _66640)). Qed.
Lemma lem5110261 {A : Type'} (lt2 : type1402 A) : (term142 A lt2) = (term143 A lt2).
Proof. exact (eq_refl (term142 A lt2)). Qed.
Lemma lem5110262 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term144 A _66640 lt2) = (term144 A _66640 lt2).
Proof. exact (eq_refl (term144 A _66640 lt2)). Qed.
Lemma lem5110263 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : ((_66640 lt2) = (term142 A lt2)) = ((_66640 lt2) = (term143 A lt2)).
Proof. exact (MK_COMB (@lem5110262 A _66640 lt2) (@lem5110261 A lt2)). Qed.
Lemma lem5110264 {A : Type'} (_66640 : type418 A) : (term201 A _66640) = (term202 A _66640).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5110263 A _66640 lt2)). Qed.
Lemma lem5110265 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5110266 {A : Type'} (_66640 : type418 A) : (term198 A _66640) = (term203 A _66640).
Proof. exact (MK_COMB (@lem5110265 A) (@lem5110264 A _66640)). Qed.
Lemma lem5110267 {A : Type'} (_66640 : type418 A) : ((_66640 = (term197 A)) = (term198 A _66640)) = ((_66640 = (term141 A)) = (term203 A _66640)).
Proof. exact (MK_COMB (@lem5110260 A _66640) (@lem5110266 A _66640)). Qed.
Lemma lem5110268 {A : Type'} (_66640 : type418 A) : (_66640 = (term141 A)) = (term203 A _66640).
Proof. exact (EQ_MP (@lem5110267 A _66640) (@lem5110254 A _66640)). Qed.
Lemma lem5110270 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term193 _3571 _3575 t)) = (term194 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5110271 {A : Type'} (s : type1402 A) (t : type1402 A) : (s = (term204 A t)) = (term205 A s t).
Proof. exact (@lem5110270 (A -> Prop) A s t). Qed.
Lemma lem5110272 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : ((_66640 lt2) = (term206 A lt2)) = (term207 A _66640 lt2).
Proof. exact (@lem5110271 A (_66640 lt2) (term143 A lt2)). Qed.
Lemma lem5110273 {A : Type'} (lt2 : type1402 A) (x : A) : (term145 A lt2 x) = (term146 A lt2 x).
Proof. exact (eq_refl (term145 A lt2 x)). Qed.
Lemma lem5110274 {A : Type'} (lt2 : type1402 A) : (term206 A lt2) = (term143 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5110273 A lt2 x)). Qed.
Lemma lem5110275 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term144 A _66640 lt2) = (term144 A _66640 lt2).
Proof. exact (eq_refl (term144 A _66640 lt2)). Qed.
Lemma lem5110276 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : ((_66640 lt2) = (term206 A lt2)) = ((_66640 lt2) = (term143 A lt2)).
Proof. exact (MK_COMB (@lem5110275 A _66640 lt2) (@lem5110274 A lt2)). Qed.
Lemma lem5110277 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5110278 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term208 A _66640 lt2) = (term209 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110277) (@lem5110276 A _66640 lt2)). Qed.
Lemma lem5110279 {A : Type'} (lt2 : type1402 A) (x : A) : (term145 A lt2 x) = (term146 A lt2 x).
Proof. exact (eq_refl (term145 A lt2 x)). Qed.
Lemma lem5110280 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term147 A _66640 lt2 x) = (term147 A _66640 lt2 x).
Proof. exact (eq_refl (term147 A _66640 lt2 x)). Qed.
Lemma lem5110281 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : ((_66640 lt2 x) = (term145 A lt2 x)) = ((_66640 lt2 x) = (term146 A lt2 x)).
Proof. exact (MK_COMB (@lem5110280 A _66640 lt2 x) (@lem5110279 A lt2 x)). Qed.
Lemma lem5110282 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term210 A _66640 lt2) = (term211 A _66640 lt2).
Proof. exact (fun_ext (fun x : A => @lem5110281 A _66640 lt2 x)). Qed.
Lemma lem5110283 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110284 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term207 A _66640 lt2) = (term212 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110283 A) (@lem5110282 A _66640 lt2)). Qed.
Lemma lem5110285 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (((_66640 lt2) = (term206 A lt2)) = (term207 A _66640 lt2)) = (((_66640 lt2) = (term143 A lt2)) = (term212 A _66640 lt2)).
Proof. exact (MK_COMB (@lem5110278 A _66640 lt2) (@lem5110284 A _66640 lt2)). Qed.
Lemma lem5110286 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : ((_66640 lt2) = (term143 A lt2)) = (term212 A _66640 lt2).
Proof. exact (EQ_MP (@lem5110285 A _66640 lt2) (@lem5110272 A _66640 lt2)). Qed.
Lemma lem5110288 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term193 _3571 _3575 t)) = (term194 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem5110289 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = (term213 A t)) = (term214 A s t).
Proof. exact (@lem5110288 Prop A s t). Qed.
Lemma lem5110290 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : ((_66640 lt2 x) = (term215 A lt2 x)) = (term216 A _66640 lt2 x).
Proof. exact (@lem5110289 A (_66640 lt2 x) (term146 A lt2 x)). Qed.
Lemma lem5110291 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term217 A lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term217 A lt2 x GEN_PVAR_227)). Qed.
Lemma lem5110292 {A : Type'} (lt2 : type1402 A) (x : A) : (term215 A lt2 x) = (term146 A lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5110291 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110293 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term147 A _66640 lt2 x) = (term147 A _66640 lt2 x).
Proof. exact (eq_refl (term147 A _66640 lt2 x)). Qed.
Lemma lem5110294 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : ((_66640 lt2 x) = (term215 A lt2 x)) = ((_66640 lt2 x) = (term146 A lt2 x)).
Proof. exact (MK_COMB (@lem5110293 A _66640 lt2 x) (@lem5110292 A lt2 x)). Qed.
Lemma lem5110295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5110296 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term219 A _66640 lt2 x) = (term220 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5110295) (@lem5110294 A _66640 lt2 x)). Qed.
Lemma lem5110297 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term217 A lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term217 A lt2 x GEN_PVAR_227)). Qed.
Lemma lem5110298 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term221 A _66640 lt2 x GEN_PVAR_227) = (term221 A _66640 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term221 A _66640 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5110299 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((_66640 lt2 x GEN_PVAR_227) = (term217 A lt2 x GEN_PVAR_227)) = ((_66640 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)).
Proof. exact (MK_COMB (@lem5110298 A _66640 lt2 x GEN_PVAR_227) (@lem5110297 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110300 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term222 A _66640 lt2 x) = (term223 A _66640 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5110299 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110301 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110302 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term216 A _66640 lt2 x) = (term224 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5110301 A) (@lem5110300 A _66640 lt2 x)). Qed.
Lemma lem5110303 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (((_66640 lt2 x) = (term215 A lt2 x)) = (term216 A _66640 lt2 x)) = (((_66640 lt2 x) = (term146 A lt2 x)) = (term224 A _66640 lt2 x)).
Proof. exact (MK_COMB (@lem5110296 A _66640 lt2 x) (@lem5110302 A _66640 lt2 x)). Qed.
Lemma lem5110304 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : ((_66640 lt2 x) = (term146 A lt2 x)) = (term224 A _66640 lt2 x).
Proof. exact (EQ_MP (@lem5110303 A _66640 lt2 x) (@lem5110290 A _66640 lt2 x)). Qed.
Lemma lem5110305 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((_66640 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)) = ((_66640 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)).
Proof. exact (eq_refl ((_66640 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x))). Qed.
Lemma lem5110306 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term223 A _66640 lt2 x) = (term223 A _66640 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5110305 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110307 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110308 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term224 A _66640 lt2 x) = (term224 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5110307 A) (@lem5110306 A _66640 lt2 x)). Qed.
Lemma lem5110309 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : ((_66640 lt2 x) = (term146 A lt2 x)) = (term224 A _66640 lt2 x).
Proof. exact (TRANS (@lem5110304 A _66640 lt2 x) (@lem5110308 A _66640 lt2 x)). Qed.
Lemma lem5110310 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term211 A _66640 lt2) = (term225 A _66640 lt2).
Proof. exact (fun_ext (fun x : A => @lem5110309 A _66640 lt2 x)). Qed.
Lemma lem5110311 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110312 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term212 A _66640 lt2) = (term226 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110311 A) (@lem5110310 A _66640 lt2)). Qed.
Lemma lem5110313 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : ((_66640 lt2) = (term143 A lt2)) = (term226 A _66640 lt2).
Proof. exact (TRANS (@lem5110286 A _66640 lt2) (@lem5110312 A _66640 lt2)). Qed.
Lemma lem5110314 {A : Type'} (_66640 : type418 A) : (term202 A _66640) = (term227 A _66640).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5110313 A _66640 lt2)). Qed.
Lemma lem5110315 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5110316 {A : Type'} (_66640 : type418 A) : (term203 A _66640) = (term228 A _66640).
Proof. exact (MK_COMB (@lem5110315 A) (@lem5110314 A _66640)). Qed.
Lemma lem5110317 {A : Type'} (_66640 : type418 A) : (_66640 = (term141 A)) = (term228 A _66640).
Proof. exact (TRANS (@lem5110268 A _66640) (@lem5110316 A _66640)). Qed.
Lemma lem5110318 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5110319 {A : Type'} (_66640 : type418 A) : (term179 A _66640) = (term229 A _66640).
Proof. exact (MK_COMB (@lem5110318) (@lem5110317 A _66640)). Qed.
Lemma lem5110320 {A : Type'} (_66640 : type418 A) : (term1033 A _66640) = (term1033 A _66640).
Proof. exact (eq_refl (term1033 A _66640)). Qed.
Lemma lem5110321 {A : Type'} (_66640 : type418 A) : (term1047 A _66640) = (term1053 A _66640).
Proof. exact (MK_COMB (@lem5110319 A _66640) (@lem5110320 A _66640)). Qed.
Lemma lem5110322 {A : Type'} : (term1049 A) = (term1054 A).
Proof. exact (fun_ext (fun _66640 : type418 A => @lem5110321 A _66640)). Qed.
Lemma lem5110323 {A : Type'} : (@all ((A -> A -> Prop) -> A -> A -> Prop)) = (@all ((A -> A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem5110324 {A : Type'} : (term1051 A) = (term1055 A).
Proof. exact (MK_COMB (@lem5110323 A) (@lem5110322 A)). Qed.
Lemma lem5110325 {A : Type'} : (term1039 A) = (term1039 A).
Proof. exact (eq_refl (term1039 A)). Qed.
Lemma lem5110326 {A : Type'} : ((term1011 A) = (term1051 A)) = ((term1011 A) = (term1055 A)).
Proof. exact (MK_COMB (@lem5110325 A) (@lem5110324 A)). Qed.
Lemma lem5110329 {A : Type'} : (term1011 A) = (term1055 A).
Proof. exact (EQ_MP (@lem5110326 A) (@lem5110250 A)). Qed.
Lemma lem5110330 {A : Type'} : (term1010 A) = (term1055 A).
Proof. exact (TRANS (@lem5110021 A) (@lem5110329 A)). Qed.
Lemma lem5110331 (n : nat) : (term1012 n) = (term1012 n).
Proof. exact (eq_refl (term1012 n)). Qed.
Lemma lem5110332 : term1013 = term1013.
Proof. exact (fun_ext (fun n : nat => @lem5110331 n)). Qed.
Lemma lem5110333 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5110334 : term985 = term985.
Proof. exact (MK_COMB (@lem5110333) (@lem5110332)). Qed.
Lemma lem5110335 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5110336 : term984 = term984.
Proof. exact (MK_COMB (@lem5110335) (@lem5110334)). Qed.
Lemma lem5110345 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term986 A lt2 x s) = (term986 A lt2 x s).
Proof. exact (eq_refl (term986 A lt2 x s)). Qed.
Lemma lem5110346 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term988 A lt2 x s) = (term988 A lt2 x s).
Proof. exact (MK_COMB (@lem5110345 A lt2 x s) (@lem5110336)). Qed.
Lemma lem5110353 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term1021 A x _66640 lt2 s) = (term1021 A x _66640 lt2 s).
Proof. exact (eq_refl (term1021 A x _66640 lt2 s)). Qed.
Lemma lem5110354 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term1022 A _66640 lt2 x s) = (term1022 A _66640 lt2 x s).
Proof. exact (MK_COMB (@lem5110353 A x _66640 lt2 s) (@lem5110346 A lt2 x s)). Qed.
Lemma lem5110359 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term104 A lt2 n s m) = (term104 A lt2 n s m).
Proof. exact (eq_refl (term104 A lt2 n s m)). Qed.
Lemma lem5110360 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term106 A lt2 s m) = (term106 A lt2 s m).
Proof. exact (fun_ext (fun n : nat => @lem5110359 A lt2 n s m)). Qed.
Lemma lem5110361 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5110362 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term108 A lt2 s m) = (term108 A lt2 s m).
Proof. exact (MK_COMB (@lem5110361) (@lem5110360 A lt2 s m)). Qed.
Lemma lem5110363 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term110 A lt2 s) = (term110 A lt2 s).
Proof. exact (fun_ext (fun m : nat => @lem5110362 A lt2 s m)). Qed.
Lemma lem5110364 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5110365 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term62 A lt2 s) = (term62 A lt2 s).
Proof. exact (MK_COMB (@lem5110364) (@lem5110363 A lt2 s)). Qed.
Lemma lem5110366 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5110367 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term640 A lt2 s) = (term640 A lt2 s).
Proof. exact (MK_COMB (@lem5110366) (@lem5110365 A lt2 s)). Qed.
Lemma lem5110368 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term1023 A _66640 lt2 x s) = (term1023 A _66640 lt2 x s).
Proof. exact (MK_COMB (@lem5110367 A lt2 s) (@lem5110354 A _66640 lt2 x s)). Qed.
Lemma lem5110369 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term94 A lt2 s n) = (term94 A lt2 s n).
Proof. exact (eq_refl (term94 A lt2 s n)). Qed.
Lemma lem5110370 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term96 A lt2 s) = (term96 A lt2 s).
Proof. exact (fun_ext (fun n : nat => @lem5110369 A lt2 s n)). Qed.
Lemma lem5110371 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5110372 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term61 A lt2 s) = (term61 A lt2 s).
Proof. exact (MK_COMB (@lem5110371) (@lem5110370 A lt2 s)). Qed.
Lemma lem5110373 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5110374 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term122 A lt2 s) = (term122 A lt2 s).
Proof. exact (MK_COMB (@lem5110373) (@lem5110372 A lt2 s)). Qed.
Lemma lem5110375 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term1024 A _66640 lt2 x s) = (term1024 A _66640 lt2 x s).
Proof. exact (MK_COMB (@lem5110374 A lt2 s) (@lem5110368 A _66640 lt2 x s)). Qed.
Lemma lem5110376 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term151 A _66640 lt2 x) = (term151 A _66640 lt2 x).
Proof. exact (eq_refl (term151 A _66640 lt2 x)). Qed.
Lemma lem5110377 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term153 A _66640 lt2) = (term153 A _66640 lt2).
Proof. exact (fun_ext (fun x : A => @lem5110376 A _66640 lt2 x)). Qed.
Lemma lem5110378 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110379 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term154 A _66640 lt2) = (term154 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110378 A) (@lem5110377 A _66640 lt2)). Qed.
Lemma lem5110380 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5110381 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term155 A _66640 lt2) = (term155 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110380) (@lem5110379 A _66640 lt2)). Qed.
Lemma lem5110382 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term1025 A _66640 lt2 x s) = (term1025 A _66640 lt2 x s).
Proof. exact (MK_COMB (@lem5110381 A _66640 lt2) (@lem5110375 A _66640 lt2 x s)). Qed.
Lemma lem5110391 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) (z : A) : (term157 A y lt2 x z) = (term157 A y lt2 x z).
Proof. exact (eq_refl (term157 A y lt2 x z)). Qed.
Lemma lem5110392 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term158 A y lt2 x) = (term158 A y lt2 x).
Proof. exact (fun_ext (fun z : A => @lem5110391 A y lt2 x z)). Qed.
Lemma lem5110393 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110394 {A : Type'} (y : A) (lt2 : type1402 A) (x : A) : (term159 A y lt2 x) = (term159 A y lt2 x).
Proof. exact (MK_COMB (@lem5110393 A) (@lem5110392 A y lt2 x)). Qed.
Lemma lem5110395 {A : Type'} (lt2 : type1402 A) (x : A) : (term160 A lt2 x) = (term160 A lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5110394 A y lt2 x)). Qed.
Lemma lem5110396 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110397 {A : Type'} (lt2 : type1402 A) (x : A) : (term161 A lt2 x) = (term161 A lt2 x).
Proof. exact (MK_COMB (@lem5110396 A) (@lem5110395 A lt2 x)). Qed.
Lemma lem5110398 {A : Type'} (lt2 : type1402 A) : (term162 A lt2) = (term162 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5110397 A lt2 x)). Qed.
Lemma lem5110399 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110400 {A : Type'} (lt2 : type1402 A) : (term58 A lt2) = (term58 A lt2).
Proof. exact (MK_COMB (@lem5110399 A) (@lem5110398 A lt2)). Qed.
Lemma lem5110401 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5110402 {A : Type'} (lt2 : type1402 A) : (term128 A lt2) = (term128 A lt2).
Proof. exact (MK_COMB (@lem5110401) (@lem5110400 A lt2)). Qed.
Lemma lem5110403 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term1026 A _66640 lt2 x s) = (term1026 A _66640 lt2 x s).
Proof. exact (MK_COMB (@lem5110402 A lt2) (@lem5110382 A _66640 lt2 x s)). Qed.
Lemma lem5110406 {A : Type'} (lt2 : type1402 A) (x : A) : (term164 A lt2 x) = (term164 A lt2 x).
Proof. exact (eq_refl (term164 A lt2 x)). Qed.
Lemma lem5110407 {A : Type'} (lt2 : type1402 A) : (term165 A lt2) = (term165 A lt2).
Proof. exact (fun_ext (fun x : A => @lem5110406 A lt2 x)). Qed.
Lemma lem5110408 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110409 {A : Type'} (lt2 : type1402 A) : (term56 A lt2) = (term56 A lt2).
Proof. exact (MK_COMB (@lem5110408 A) (@lem5110407 A lt2)). Qed.
Lemma lem5110410 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5110411 {A : Type'} (lt2 : type1402 A) : (term131 A lt2) = (term131 A lt2).
Proof. exact (MK_COMB (@lem5110410) (@lem5110409 A lt2)). Qed.
Lemma lem5110412 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term1027 A _66640 lt2 x s) = (term1027 A _66640 lt2 x s).
Proof. exact (MK_COMB (@lem5110411 A lt2) (@lem5110403 A _66640 lt2 x s)). Qed.
Lemma lem5110413 {A : Type'} (_66640 : type418 A) (x : nat) (s : nat -> A) : (term1028 A _66640 x s) = (term1028 A _66640 x s).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5110412 A _66640 lt2 x s)). Qed.
Lemma lem5110414 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5110415 {A : Type'} (_66640 : type418 A) (x : nat) (s : nat -> A) : (term1029 A _66640 x s) = (term1029 A _66640 x s).
Proof. exact (MK_COMB (@lem5110414 A) (@lem5110413 A _66640 x s)). Qed.
Lemma lem5110416 {A : Type'} (_66640 : type418 A) (s : nat -> A) : (term1030 A _66640 s) = (term1030 A _66640 s).
Proof. exact (fun_ext (fun x : nat => @lem5110415 A _66640 x s)). Qed.
Lemma lem5110417 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5110418 {A : Type'} (_66640 : type418 A) (s : nat -> A) : (term1031 A _66640 s) = (term1031 A _66640 s).
Proof. exact (MK_COMB (@lem5110417) (@lem5110416 A _66640 s)). Qed.
Lemma lem5110419 {A : Type'} (_66640 : type418 A) : (term1032 A _66640) = (term1032 A _66640).
Proof. exact (fun_ext (fun s : nat -> A => @lem5110418 A _66640 s)). Qed.
Lemma lem5110420 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem5110421 {A : Type'} (_66640 : type418 A) : (term1033 A _66640) = (term1033 A _66640).
Proof. exact (MK_COMB (@lem5110420 A) (@lem5110419 A _66640)). Qed.
Lemma lem5110422 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term233 A GEN_PVAR_227 lt2 x y) = (term233 A GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term233 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5110423 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term234 A GEN_PVAR_227 lt2 x) = (term234 A GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5110422 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5110424 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5110425 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term218 A GEN_PVAR_227 lt2 x) = (term218 A GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5110424 A) (@lem5110423 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110428 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term221 A _66640 lt2 x GEN_PVAR_227) = (term221 A _66640 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term221 A _66640 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5110429 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((_66640 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)) = ((_66640 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)).
Proof. exact (MK_COMB (@lem5110428 A _66640 lt2 x GEN_PVAR_227) (@lem5110425 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110430 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term223 A _66640 lt2 x) = (term223 A _66640 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5110429 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110431 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110432 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term224 A _66640 lt2 x) = (term224 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5110431 A) (@lem5110430 A _66640 lt2 x)). Qed.
Lemma lem5110433 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term225 A _66640 lt2) = (term225 A _66640 lt2).
Proof. exact (fun_ext (fun x : A => @lem5110432 A _66640 lt2 x)). Qed.
Lemma lem5110434 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110435 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term226 A _66640 lt2) = (term226 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110434 A) (@lem5110433 A _66640 lt2)). Qed.
Lemma lem5110436 {A : Type'} (_66640 : type418 A) : (term227 A _66640) = (term227 A _66640).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5110435 A _66640 lt2)). Qed.
Lemma lem5110437 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5110438 {A : Type'} (_66640 : type418 A) : (term228 A _66640) = (term228 A _66640).
Proof. exact (MK_COMB (@lem5110437 A) (@lem5110436 A _66640)). Qed.
Lemma lem5110439 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5110440 {A : Type'} (_66640 : type418 A) : (term229 A _66640) = (term229 A _66640).
Proof. exact (MK_COMB (@lem5110439) (@lem5110438 A _66640)). Qed.
Lemma lem5110441 {A : Type'} (_66640 : type418 A) : (term1053 A _66640) = (term1053 A _66640).
Proof. exact (MK_COMB (@lem5110440 A _66640) (@lem5110421 A _66640)). Qed.
Lemma lem5110442 {A : Type'} : (term1054 A) = (term1054 A).
Proof. exact (fun_ext (fun _66640 : type418 A => @lem5110441 A _66640)). Qed.
Lemma lem5110443 {A : Type'} : (@all ((A -> A -> Prop) -> A -> A -> Prop)) = (@all ((A -> A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@all ((A -> A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem5110444 {A : Type'} : (term1055 A) = (term1055 A).
Proof. exact (MK_COMB (@lem5110443 A) (@lem5110442 A)). Qed.
Lemma lem5110575 {A : Type'} : (term1010 A) = (term1055 A).
Proof. exact (TRANS (@lem5110330 A) (@lem5110444 A)). Qed.
Lemma lem5110576 {A : Type'} : (term1055 A) = (term1010 A).
Proof. exact (SYM (@lem5110575 A)). Qed.
Lemma lem5110577 {A : Type'} (_66640 : type418 A) (h1 : term228 A _66640) : term228 A _66640.
Proof. exact (h1). Qed.
Lemma lem5110582 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term62 A lt2 s.
Proof. exact (h1). Qed.
Lemma lem5110584 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term978 A lt2 x s) : term978 A lt2 x s.
Proof. exact (h1). Qed.
Lemma lem5110585 (h1 : term985) : term985.
Proof. exact (h1). Qed.
Lemma lem5110589 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term233 A GEN_PVAR_227 lt2 x y) = (term233 A GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term233 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5110590 {A : Type'} (P : A -> Prop) : (term235 A P) = (term236 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5110591 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term237 A GEN_PVAR_227 lt2 x) = (term238 A GEN_PVAR_227 lt2 x).
Proof. exact (@lem5110590 A (term234 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110592 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term239 A GEN_PVAR_227 lt2 x y) = (term233 A GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term239 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5110593 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5110595 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term240 A GEN_PVAR_227 lt2 x y) = (term241 A GEN_PVAR_227 lt2 x y).
Proof. exact (MK_COMB (@lem5110593) (@lem5110592 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5110596 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term242 A GEN_PVAR_227 lt2 x) = (term243 A GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5110595 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5110597 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110598 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term238 A GEN_PVAR_227 lt2 x) = (term244 A GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5110597 A) (@lem5110596 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110599 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term237 A GEN_PVAR_227 lt2 x) = (term244 A GEN_PVAR_227 lt2 x).
Proof. exact (TRANS (@lem5110591 A GEN_PVAR_227 lt2 x) (@lem5110598 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110600 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term234 A GEN_PVAR_227 lt2 x) = (term234 A GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5110589 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5110601 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5110602 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term218 A GEN_PVAR_227 lt2 x) = (term218 A GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5110601 A) (@lem5110600 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110604 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term245 A _66640 lt2 x GEN_PVAR_227) = (term245 A _66640 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term245 A _66640 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5110605 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term246 A _66640 GEN_PVAR_227 lt2 x) = (term246 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5110604 A _66640 lt2 x GEN_PVAR_227) (@lem5110602 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110607 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term247 A _66640 lt2 x GEN_PVAR_227) = (term247 A _66640 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term247 A _66640 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5110608 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term248 A _66640 GEN_PVAR_227 lt2 x) = (term249 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5110607 A _66640 lt2 x GEN_PVAR_227) (@lem5110599 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5110610 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term250 A _66640 GEN_PVAR_227 lt2 x) = (term251 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5110609) (@lem5110608 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110611 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term252 A _66640 GEN_PVAR_227 lt2 x) = (term253 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5110610 A _66640 GEN_PVAR_227 lt2 x) (@lem5110605 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110612 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((_66640 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)) = (term252 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (@lem17784 (_66640 lt2 x GEN_PVAR_227) (term218 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110613 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((_66640 lt2 x GEN_PVAR_227) = (term218 A GEN_PVAR_227 lt2 x)) = (term253 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (TRANS (@lem5110612 A _66640 GEN_PVAR_227 lt2 x) (@lem5110611 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110614 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term223 A _66640 lt2 x) = (term254 A _66640 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5110613 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110615 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110616 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term224 A _66640 lt2 x) = (term255 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5110615 A) (@lem5110614 A _66640 lt2 x)). Qed.
Lemma lem5110617 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term225 A _66640 lt2) = (term256 A _66640 lt2).
Proof. exact (fun_ext (fun x : A => @lem5110616 A _66640 lt2 x)). Qed.
Lemma lem5110618 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110619 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term226 A _66640 lt2) = (term257 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110618 A) (@lem5110617 A _66640 lt2)). Qed.
Lemma lem5110620 {A : Type'} (_66640 : type418 A) : (term227 A _66640) = (term258 A _66640).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5110619 A _66640 lt2)). Qed.
Lemma lem5110621 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5110622 {A : Type'} (_66640 : type418 A) : (term228 A _66640) = (term259 A _66640).
Proof. exact (MK_COMB (@lem5110621 A) (@lem5110620 A _66640)). Qed.
Lemma lem5110632 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5110633 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (@lem5110632 A P Q). Qed.
Lemma lem5110634 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term262 A _66640 lt2 x) = (term263 A _66640 lt2 x).
Proof. exact (@lem5110633 A (term264 A _66640 lt2 x) (term265 A _66640 lt2 x)). Qed.
Lemma lem5110635 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term266 A _66640 lt2 x GEN_PVAR_227) = (term249 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term266 A _66640 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5110636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5110637 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term267 A _66640 lt2 x GEN_PVAR_227) = (term251 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5110636) (@lem5110635 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110638 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term268 A _66640 lt2 x GEN_PVAR_227) = (term246 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term268 A _66640 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5110639 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term269 A _66640 lt2 x GEN_PVAR_227) = (term253 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5110637 A _66640 GEN_PVAR_227 lt2 x) (@lem5110638 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110640 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term270 A _66640 lt2 x) = (term254 A _66640 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5110639 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110641 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110642 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term262 A _66640 lt2 x) = (term255 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5110641 A) (@lem5110640 A _66640 lt2 x)). Qed.
Lemma lem5110643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5110644 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term271 A _66640 lt2 x) = (term272 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5110643) (@lem5110642 A _66640 lt2 x)). Qed.
Lemma lem5110645 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term266 A _66640 lt2 x GEN_PVAR_227) = (term249 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term266 A _66640 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5110646 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term273 A _66640 lt2 x) = (term264 A _66640 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5110645 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110647 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110648 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term274 A _66640 lt2 x) = (term275 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5110647 A) (@lem5110646 A _66640 lt2 x)). Qed.
Lemma lem5110649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5110650 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term276 A _66640 lt2 x) = (term277 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5110649) (@lem5110648 A _66640 lt2 x)). Qed.
Lemma lem5110651 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term268 A _66640 lt2 x GEN_PVAR_227) = (term246 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term268 A _66640 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5110652 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term278 A _66640 lt2 x) = (term265 A _66640 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5110651 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5110653 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110654 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term279 A _66640 lt2 x) = (term280 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5110653 A) (@lem5110652 A _66640 lt2 x)). Qed.
Lemma lem5110655 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term263 A _66640 lt2 x) = (term281 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5110650 A _66640 lt2 x) (@lem5110654 A _66640 lt2 x)). Qed.
Lemma lem5110656 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : ((term262 A _66640 lt2 x) = (term263 A _66640 lt2 x)) = ((term255 A _66640 lt2 x) = (term281 A _66640 lt2 x)).
Proof. exact (MK_COMB (@lem5110644 A _66640 lt2 x) (@lem5110655 A _66640 lt2 x)). Qed.
Lemma lem5110657 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term255 A _66640 lt2 x) = (term281 A _66640 lt2 x).
Proof. exact (EQ_MP (@lem5110656 A _66640 lt2 x) (@lem5110634 A _66640 lt2 x)). Qed.
Lemma lem5110762 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term256 A _66640 lt2) = (term282 A _66640 lt2).
Proof. exact (fun_ext (fun x : A => @lem5110657 A _66640 lt2 x)). Qed.
Lemma lem5110763 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110764 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term257 A _66640 lt2) = (term283 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110763 A) (@lem5110762 A _66640 lt2)). Qed.
Lemma lem5110766 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5110767 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (@lem5110766 A P Q). Qed.
Lemma lem5110768 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term284 A _66640 lt2) = (term285 A _66640 lt2).
Proof. exact (@lem5110767 A (term286 A _66640 lt2) (term287 A _66640 lt2)). Qed.
Lemma lem5110769 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term288 A _66640 lt2 x) = (term275 A _66640 lt2 x).
Proof. exact (eq_refl (term288 A _66640 lt2 x)). Qed.
Lemma lem5110770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5110771 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term289 A _66640 lt2 x) = (term277 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5110770) (@lem5110769 A _66640 lt2 x)). Qed.
Lemma lem5110772 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term290 A _66640 lt2 x) = (term280 A _66640 lt2 x).
Proof. exact (eq_refl (term290 A _66640 lt2 x)). Qed.
Lemma lem5110773 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term291 A _66640 lt2 x) = (term281 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5110771 A _66640 lt2 x) (@lem5110772 A _66640 lt2 x)). Qed.
Lemma lem5110774 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term292 A _66640 lt2) = (term282 A _66640 lt2).
Proof. exact (fun_ext (fun x : A => @lem5110773 A _66640 lt2 x)). Qed.
Lemma lem5110775 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110776 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term284 A _66640 lt2) = (term283 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110775 A) (@lem5110774 A _66640 lt2)). Qed.
Lemma lem5110777 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5110778 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term293 A _66640 lt2) = (term294 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110777) (@lem5110776 A _66640 lt2)). Qed.
Lemma lem5110779 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term288 A _66640 lt2 x) = (term275 A _66640 lt2 x).
Proof. exact (eq_refl (term288 A _66640 lt2 x)). Qed.
Lemma lem5110780 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term295 A _66640 lt2) = (term286 A _66640 lt2).
Proof. exact (fun_ext (fun x : A => @lem5110779 A _66640 lt2 x)). Qed.
Lemma lem5110781 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110782 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term296 A _66640 lt2) = (term297 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110781 A) (@lem5110780 A _66640 lt2)). Qed.
Lemma lem5110783 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5110784 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term298 A _66640 lt2) = (term299 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110783) (@lem5110782 A _66640 lt2)). Qed.
Lemma lem5110785 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term290 A _66640 lt2 x) = (term280 A _66640 lt2 x).
Proof. exact (eq_refl (term290 A _66640 lt2 x)). Qed.
Lemma lem5110786 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term300 A _66640 lt2) = (term287 A _66640 lt2).
Proof. exact (fun_ext (fun x : A => @lem5110785 A _66640 lt2 x)). Qed.
Lemma lem5110787 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5110788 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term301 A _66640 lt2) = (term302 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110787 A) (@lem5110786 A _66640 lt2)). Qed.
Lemma lem5110789 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term285 A _66640 lt2) = (term303 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110784 A _66640 lt2) (@lem5110788 A _66640 lt2)). Qed.
Lemma lem5110790 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : ((term284 A _66640 lt2) = (term285 A _66640 lt2)) = ((term283 A _66640 lt2) = (term303 A _66640 lt2)).
Proof. exact (MK_COMB (@lem5110778 A _66640 lt2) (@lem5110789 A _66640 lt2)). Qed.
Lemma lem5110791 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term283 A _66640 lt2) = (term303 A _66640 lt2).
Proof. exact (EQ_MP (@lem5110790 A _66640 lt2) (@lem5110768 A _66640 lt2)). Qed.
Lemma lem5110904 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term257 A _66640 lt2) = (term303 A _66640 lt2).
Proof. exact (TRANS (@lem5110764 A _66640 lt2) (@lem5110791 A _66640 lt2)). Qed.
Lemma lem5110905 {A : Type'} (_66640 : type418 A) : (term258 A _66640) = (term304 A _66640).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5110904 A _66640 lt2)). Qed.
Lemma lem5110906 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5110907 {A : Type'} (_66640 : type418 A) : (term259 A _66640) = (term305 A _66640).
Proof. exact (MK_COMB (@lem5110906 A) (@lem5110905 A _66640)). Qed.
Lemma lem5110909 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term260 A P Q) = (term261 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5110910 {A : Type'} (P : type421 A) (Q : type421 A) : (term306 A P Q) = (term307 A P Q).
Proof. exact (@lem5110909 (type1402 A) P Q). Qed.
Lemma lem5110911 {A : Type'} (_66640 : type418 A) : (term308 A _66640) = (term309 A _66640).
Proof. exact (@lem5110910 A (term310 A _66640) (term311 A _66640)). Qed.
Lemma lem5110912 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term312 A _66640 lt2) = (term297 A _66640 lt2).
Proof. exact (eq_refl (term312 A _66640 lt2)). Qed.
Lemma lem5110913 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5110914 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term313 A _66640 lt2) = (term299 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110913) (@lem5110912 A _66640 lt2)). Qed.
Lemma lem5110915 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term314 A _66640 lt2) = (term302 A _66640 lt2).
Proof. exact (eq_refl (term314 A _66640 lt2)). Qed.
Lemma lem5110916 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term315 A _66640 lt2) = (term303 A _66640 lt2).
Proof. exact (MK_COMB (@lem5110914 A _66640 lt2) (@lem5110915 A _66640 lt2)). Qed.
Lemma lem5110917 {A : Type'} (_66640 : type418 A) : (term316 A _66640) = (term304 A _66640).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5110916 A _66640 lt2)). Qed.
Lemma lem5110918 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5110919 {A : Type'} (_66640 : type418 A) : (term308 A _66640) = (term305 A _66640).
Proof. exact (MK_COMB (@lem5110918 A) (@lem5110917 A _66640)). Qed.
Lemma lem5110920 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5110921 {A : Type'} (_66640 : type418 A) : (term317 A _66640) = (term318 A _66640).
Proof. exact (MK_COMB (@lem5110920) (@lem5110919 A _66640)). Qed.
Lemma lem5110922 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term312 A _66640 lt2) = (term297 A _66640 lt2).
Proof. exact (eq_refl (term312 A _66640 lt2)). Qed.
Lemma lem5110923 {A : Type'} (_66640 : type418 A) : (term319 A _66640) = (term310 A _66640).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5110922 A _66640 lt2)). Qed.
Lemma lem5110924 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5110925 {A : Type'} (_66640 : type418 A) : (term320 A _66640) = (term321 A _66640).
Proof. exact (MK_COMB (@lem5110924 A) (@lem5110923 A _66640)). Qed.
Lemma lem5110926 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5110927 {A : Type'} (_66640 : type418 A) : (term322 A _66640) = (term323 A _66640).
Proof. exact (MK_COMB (@lem5110926) (@lem5110925 A _66640)). Qed.
Lemma lem5110928 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term314 A _66640 lt2) = (term302 A _66640 lt2).
Proof. exact (eq_refl (term314 A _66640 lt2)). Qed.
Lemma lem5110929 {A : Type'} (_66640 : type418 A) : (term324 A _66640) = (term311 A _66640).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5110928 A _66640 lt2)). Qed.
Lemma lem5110930 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5110931 {A : Type'} (_66640 : type418 A) : (term325 A _66640) = (term326 A _66640).
Proof. exact (MK_COMB (@lem5110930 A) (@lem5110929 A _66640)). Qed.
Lemma lem5110932 {A : Type'} (_66640 : type418 A) : (term309 A _66640) = (term327 A _66640).
Proof. exact (MK_COMB (@lem5110927 A _66640) (@lem5110931 A _66640)). Qed.
Lemma lem5110933 {A : Type'} (_66640 : type418 A) : ((term308 A _66640) = (term309 A _66640)) = ((term305 A _66640) = (term327 A _66640)).
Proof. exact (MK_COMB (@lem5110921 A _66640) (@lem5110932 A _66640)). Qed.
Lemma lem5110934 {A : Type'} (_66640 : type418 A) : (term305 A _66640) = (term327 A _66640).
Proof. exact (EQ_MP (@lem5110933 A _66640) (@lem5110911 A _66640)). Qed.
Lemma lem5111055 {A : Type'} (_66640 : type418 A) : (term259 A _66640) = (term327 A _66640).
Proof. exact (TRANS (@lem5110907 A _66640) (@lem5110934 A _66640)). Qed.
Lemma lem5111057 {A : Type'} (P : Prop) (Q : A -> Prop) : (term328 A P Q) = (term329 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5111058 {A : Type'} (P : Prop) (Q : A -> Prop) : (term328 A P Q) = (term329 A P Q).
Proof. exact (@lem5111057 A P Q). Qed.
Lemma lem5111059 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term330 A _66640 GEN_PVAR_227 lt2 x) = (term331 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (@lem5111058 A (term332 A _66640 lt2 x GEN_PVAR_227) (term234 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5111060 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term239 A GEN_PVAR_227 lt2 x y) = (term233 A GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term239 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5111061 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term333 A GEN_PVAR_227 lt2 x) = (term234 A GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5111060 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5111062 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5111063 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term334 A GEN_PVAR_227 lt2 x) = (term218 A GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5111062 A) (@lem5111061 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5111064 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term245 A _66640 lt2 x GEN_PVAR_227) = (term245 A _66640 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term245 A _66640 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5111065 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term330 A _66640 GEN_PVAR_227 lt2 x) = (term246 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5111064 A _66640 lt2 x GEN_PVAR_227) (@lem5111063 A GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5111066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5111067 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term335 A _66640 GEN_PVAR_227 lt2 x) = (term336 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5111066) (@lem5111065 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5111068 {A : Type'} (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term239 A GEN_PVAR_227 lt2 x y) = (term233 A GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term239 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5111069 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) (GEN_PVAR_227 : A) : (term245 A _66640 lt2 x GEN_PVAR_227) = (term245 A _66640 lt2 x GEN_PVAR_227).
Proof. exact (eq_refl (term245 A _66640 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5111070 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term337 A _66640 GEN_PVAR_227 lt2 x y) = (term338 A _66640 GEN_PVAR_227 lt2 x y).
Proof. exact (MK_COMB (@lem5111069 A _66640 lt2 x GEN_PVAR_227) (@lem5111068 A GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5111071 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term339 A _66640 GEN_PVAR_227 lt2 x) = (term340 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5111070 A _66640 GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5111072 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5111073 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term331 A _66640 GEN_PVAR_227 lt2 x) = (term341 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5111072 A) (@lem5111071 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5111074 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : ((term330 A _66640 GEN_PVAR_227 lt2 x) = (term331 A _66640 GEN_PVAR_227 lt2 x)) = ((term246 A _66640 GEN_PVAR_227 lt2 x) = (term341 A _66640 GEN_PVAR_227 lt2 x)).
Proof. exact (MK_COMB (@lem5111067 A _66640 GEN_PVAR_227 lt2 x) (@lem5111073 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5111075 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term246 A _66640 GEN_PVAR_227 lt2 x) = (term341 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (EQ_MP (@lem5111074 A _66640 GEN_PVAR_227 lt2 x) (@lem5111059 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5111076 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term265 A _66640 lt2 x) = (term342 A _66640 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5111075 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5111077 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5111078 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term280 A _66640 lt2 x) = (term343 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5111077 A) (@lem5111076 A _66640 lt2 x)). Qed.
Lemma lem5111080 {A B : Type'} (P : type1413 A B) : (term344 A B P) = (term345 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5111081 {A : Type'} (P : type1402 A) : (term346 A P) = (term347 A P).
Proof. exact (@lem5111080 A A P). Qed.
Lemma lem5111082 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term348 A _66640 lt2 x) = (term349 A _66640 lt2 x).
Proof. exact (@lem5111081 A (term350 A _66640 lt2 x)). Qed.
Lemma lem5111083 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term351 A _66640 lt2 x GEN_PVAR_227) = (term340 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term351 A _66640 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5111084 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5111085 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term352 A _66640 lt2 x GEN_PVAR_227 y) = (term353 A _66640 GEN_PVAR_227 lt2 x y).
Proof. exact (MK_COMB (@lem5111083 A _66640 GEN_PVAR_227 lt2 x) (@lem5111084 A y)). Qed.
Lemma lem5111086 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term353 A _66640 GEN_PVAR_227 lt2 x y) = (term338 A _66640 GEN_PVAR_227 lt2 x y).
Proof. exact (eq_refl (term353 A _66640 GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5111087 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) (y : A) : (term352 A _66640 lt2 x GEN_PVAR_227 y) = (term338 A _66640 GEN_PVAR_227 lt2 x y).
Proof. exact (TRANS (@lem5111085 A _66640 GEN_PVAR_227 lt2 x y) (@lem5111086 A _66640 GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5111088 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term354 A _66640 lt2 x GEN_PVAR_227) = (term340 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (fun_ext (fun y : A => @lem5111087 A _66640 GEN_PVAR_227 lt2 x y)). Qed.
Lemma lem5111089 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5111090 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term355 A _66640 lt2 x GEN_PVAR_227) = (term341 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (MK_COMB (@lem5111089 A) (@lem5111088 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5111091 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term356 A _66640 lt2 x) = (term342 A _66640 lt2 x).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5111090 A _66640 GEN_PVAR_227 lt2 x)). Qed.
Lemma lem5111092 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5111093 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term348 A _66640 lt2 x) = (term343 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5111092 A) (@lem5111091 A _66640 lt2 x)). Qed.
Lemma lem5111094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5111095 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term357 A _66640 lt2 x) = (term358 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5111094) (@lem5111093 A _66640 lt2 x)). Qed.
Lemma lem5111096 {A : Type'} (_66640 : type418 A) (GEN_PVAR_227 : A) (lt2 : type1402 A) (x : A) : (term351 A _66640 lt2 x GEN_PVAR_227) = (term340 A _66640 GEN_PVAR_227 lt2 x).
Proof. exact (eq_refl (term351 A _66640 lt2 x GEN_PVAR_227)). Qed.
Lemma lem5111097 {A : Type'} (y : A -> A) (GEN_PVAR_227 : A) : (y GEN_PVAR_227) = (y GEN_PVAR_227).
Proof. exact (eq_refl (y GEN_PVAR_227)). Qed.
Lemma lem5111098 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) (GEN_PVAR_227 : A) : (term359 A _66640 lt2 x y GEN_PVAR_227) = (term360 A _66640 lt2 x y GEN_PVAR_227).
Proof. exact (MK_COMB (@lem5111096 A _66640 GEN_PVAR_227 lt2 x) (@lem5111097 A y GEN_PVAR_227)). Qed.
Lemma lem5111099 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) (GEN_PVAR_227 : A) : (term360 A _66640 lt2 x y GEN_PVAR_227) = (term361 A _66640 lt2 x y GEN_PVAR_227).
Proof. exact (eq_refl (term360 A _66640 lt2 x y GEN_PVAR_227)). Qed.
Lemma lem5111100 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) (GEN_PVAR_227 : A) : (term359 A _66640 lt2 x y GEN_PVAR_227) = (term361 A _66640 lt2 x y GEN_PVAR_227).
Proof. exact (TRANS (@lem5111098 A _66640 lt2 x y GEN_PVAR_227) (@lem5111099 A _66640 lt2 x y GEN_PVAR_227)). Qed.
Lemma lem5111101 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) : (term362 A _66640 lt2 x y) = (term363 A _66640 lt2 x y).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A => @lem5111100 A _66640 lt2 x y GEN_PVAR_227)). Qed.
Lemma lem5111102 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5111103 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) : (term364 A _66640 lt2 x y) = (term365 A _66640 lt2 x y).
Proof. exact (MK_COMB (@lem5111102 A) (@lem5111101 A _66640 lt2 x y)). Qed.
Lemma lem5111104 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term366 A _66640 lt2 x) = (term367 A _66640 lt2 x).
Proof. exact (fun_ext (fun y : A -> A => @lem5111103 A _66640 lt2 x y)). Qed.
Lemma lem5111105 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem5111106 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term349 A _66640 lt2 x) = (term368 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5111105 A) (@lem5111104 A _66640 lt2 x)). Qed.
Lemma lem5111107 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : ((term348 A _66640 lt2 x) = (term349 A _66640 lt2 x)) = ((term343 A _66640 lt2 x) = (term368 A _66640 lt2 x)).
Proof. exact (MK_COMB (@lem5111095 A _66640 lt2 x) (@lem5111106 A _66640 lt2 x)). Qed.
Lemma lem5111108 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term343 A _66640 lt2 x) = (term368 A _66640 lt2 x).
Proof. exact (EQ_MP (@lem5111107 A _66640 lt2 x) (@lem5111082 A _66640 lt2 x)). Qed.
Lemma lem5111109 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term280 A _66640 lt2 x) = (term368 A _66640 lt2 x).
Proof. exact (TRANS (@lem5111078 A _66640 lt2 x) (@lem5111108 A _66640 lt2 x)). Qed.
Lemma lem5111110 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term287 A _66640 lt2) = (term369 A _66640 lt2).
Proof. exact (fun_ext (fun x : A => @lem5111109 A _66640 lt2 x)). Qed.
Lemma lem5111111 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5111112 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term302 A _66640 lt2) = (term370 A _66640 lt2).
Proof. exact (MK_COMB (@lem5111111 A) (@lem5111110 A _66640 lt2)). Qed.
Lemma lem5111114 {A B : Type'} (P : type1413 A B) : (term344 A B P) = (term345 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5111115 {A : Type'} (P : type1359 A) : (term371 A P) = (term372 A P).
Proof. exact (@lem5111114 A (A -> A) P). Qed.
Lemma lem5111116 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term373 A _66640 lt2) = (term374 A _66640 lt2).
Proof. exact (@lem5111115 A (term375 A _66640 lt2)). Qed.
Lemma lem5111117 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term376 A _66640 lt2 x) = (term367 A _66640 lt2 x).
Proof. exact (eq_refl (term376 A _66640 lt2 x)). Qed.
Lemma lem5111118 {A : Type'} (y : A -> A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5111119 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) : (term377 A _66640 lt2 x y) = (term378 A _66640 lt2 x y).
Proof. exact (MK_COMB (@lem5111117 A _66640 lt2 x) (@lem5111118 A y)). Qed.
Lemma lem5111120 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) : (term378 A _66640 lt2 x y) = (term365 A _66640 lt2 x y).
Proof. exact (eq_refl (term378 A _66640 lt2 x y)). Qed.
Lemma lem5111121 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) (y : A -> A) : (term377 A _66640 lt2 x y) = (term365 A _66640 lt2 x y).
Proof. exact (TRANS (@lem5111119 A _66640 lt2 x y) (@lem5111120 A _66640 lt2 x y)). Qed.
Lemma lem5111122 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term379 A _66640 lt2 x) = (term367 A _66640 lt2 x).
Proof. exact (fun_ext (fun y : A -> A => @lem5111121 A _66640 lt2 x y)). Qed.
Lemma lem5111123 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem5111124 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term380 A _66640 lt2 x) = (term368 A _66640 lt2 x).
Proof. exact (MK_COMB (@lem5111123 A) (@lem5111122 A _66640 lt2 x)). Qed.
Lemma lem5111125 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term381 A _66640 lt2) = (term369 A _66640 lt2).
Proof. exact (fun_ext (fun x : A => @lem5111124 A _66640 lt2 x)). Qed.
Lemma lem5111126 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5111127 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term373 A _66640 lt2) = (term370 A _66640 lt2).
Proof. exact (MK_COMB (@lem5111126 A) (@lem5111125 A _66640 lt2)). Qed.
Lemma lem5111128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5111129 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term382 A _66640 lt2) = (term383 A _66640 lt2).
Proof. exact (MK_COMB (@lem5111128) (@lem5111127 A _66640 lt2)). Qed.
Lemma lem5111130 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (x : A) : (term376 A _66640 lt2 x) = (term367 A _66640 lt2 x).
Proof. exact (eq_refl (term376 A _66640 lt2 x)). Qed.
Lemma lem5111131 {A : Type'} (y : type1400 A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem5111132 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (y : type1400 A) (x : A) : (term384 A _66640 lt2 y x) = (term385 A _66640 lt2 y x).
Proof. exact (MK_COMB (@lem5111130 A _66640 lt2 x) (@lem5111131 A y x)). Qed.
Lemma lem5111133 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (y : type1400 A) (x : A) : (term385 A _66640 lt2 y x) = (term386 A _66640 lt2 y x).
Proof. exact (eq_refl (term385 A _66640 lt2 y x)). Qed.
Lemma lem5111134 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (y : type1400 A) (x : A) : (term384 A _66640 lt2 y x) = (term386 A _66640 lt2 y x).
Proof. exact (TRANS (@lem5111132 A _66640 lt2 y x) (@lem5111133 A _66640 lt2 y x)). Qed.
Lemma lem5111135 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (y : type1400 A) : (term387 A _66640 lt2 y) = (term388 A _66640 lt2 y).
Proof. exact (fun_ext (fun x : A => @lem5111134 A _66640 lt2 y x)). Qed.
Lemma lem5111136 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5111137 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (y : type1400 A) : (term389 A _66640 lt2 y) = (term390 A _66640 lt2 y).
Proof. exact (MK_COMB (@lem5111136 A) (@lem5111135 A _66640 lt2 y)). Qed.
Lemma lem5111138 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term391 A _66640 lt2) = (term392 A _66640 lt2).
Proof. exact (fun_ext (fun y : type1400 A => @lem5111137 A _66640 lt2 y)). Qed.
Lemma lem5111139 {A : Type'} : (@ex (A -> A -> A)) = (@ex (A -> A -> A)).
Proof. exact (eq_refl (@ex (A -> A -> A))). Qed.
Lemma lem5111140 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term374 A _66640 lt2) = (term393 A _66640 lt2).
Proof. exact (MK_COMB (@lem5111139 A) (@lem5111138 A _66640 lt2)). Qed.
Lemma lem5111141 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : ((term373 A _66640 lt2) = (term374 A _66640 lt2)) = ((term370 A _66640 lt2) = (term393 A _66640 lt2)).
Proof. exact (MK_COMB (@lem5111129 A _66640 lt2) (@lem5111140 A _66640 lt2)). Qed.
Lemma lem5111142 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term370 A _66640 lt2) = (term393 A _66640 lt2).
Proof. exact (EQ_MP (@lem5111141 A _66640 lt2) (@lem5111116 A _66640 lt2)). Qed.
Lemma lem5111143 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term302 A _66640 lt2) = (term393 A _66640 lt2).
Proof. exact (TRANS (@lem5111112 A _66640 lt2) (@lem5111142 A _66640 lt2)). Qed.
Lemma lem5111144 {A : Type'} (_66640 : type418 A) : (term311 A _66640) = (term394 A _66640).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5111143 A _66640 lt2)). Qed.
Lemma lem5111145 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5111146 {A : Type'} (_66640 : type418 A) : (term326 A _66640) = (term395 A _66640).
Proof. exact (MK_COMB (@lem5111145 A) (@lem5111144 A _66640)). Qed.
Lemma lem5111148 {A B : Type'} (P : type1413 A B) : (term344 A B P) = (term345 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5111149 {A : Type'} (P : type412 A) : (term396 A P) = (term397 A P).
Proof. exact (@lem5111148 (type1402 A) (type1400 A) P). Qed.
Lemma lem5111150 {A : Type'} (_66640 : type418 A) : (term398 A _66640) = (term399 A _66640).
Proof. exact (@lem5111149 A (term400 A _66640)). Qed.
Lemma lem5111151 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term401 A _66640 lt2) = (term392 A _66640 lt2).
Proof. exact (eq_refl (term401 A _66640 lt2)). Qed.
Lemma lem5111152 {A : Type'} (y : type1400 A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5111153 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (y : type1400 A) : (term402 A _66640 lt2 y) = (term403 A _66640 lt2 y).
Proof. exact (MK_COMB (@lem5111151 A _66640 lt2) (@lem5111152 A y)). Qed.
Lemma lem5111154 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (y : type1400 A) : (term403 A _66640 lt2 y) = (term390 A _66640 lt2 y).
Proof. exact (eq_refl (term403 A _66640 lt2 y)). Qed.
Lemma lem5111155 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (y : type1400 A) : (term402 A _66640 lt2 y) = (term390 A _66640 lt2 y).
Proof. exact (TRANS (@lem5111153 A _66640 lt2 y) (@lem5111154 A _66640 lt2 y)). Qed.
Lemma lem5111156 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term404 A _66640 lt2) = (term392 A _66640 lt2).
Proof. exact (fun_ext (fun y : type1400 A => @lem5111155 A _66640 lt2 y)). Qed.
Lemma lem5111157 {A : Type'} : (@ex (A -> A -> A)) = (@ex (A -> A -> A)).
Proof. exact (eq_refl (@ex (A -> A -> A))). Qed.
Lemma lem5111158 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term405 A _66640 lt2) = (term393 A _66640 lt2).
Proof. exact (MK_COMB (@lem5111157 A) (@lem5111156 A _66640 lt2)). Qed.
Lemma lem5111159 {A : Type'} (_66640 : type418 A) : (term406 A _66640) = (term394 A _66640).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5111158 A _66640 lt2)). Qed.
Lemma lem5111160 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5111161 {A : Type'} (_66640 : type418 A) : (term398 A _66640) = (term395 A _66640).
Proof. exact (MK_COMB (@lem5111160 A) (@lem5111159 A _66640)). Qed.
Lemma lem5111162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5111163 {A : Type'} (_66640 : type418 A) : (term407 A _66640) = (term408 A _66640).
Proof. exact (MK_COMB (@lem5111162) (@lem5111161 A _66640)). Qed.
Lemma lem5111164 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (term401 A _66640 lt2) = (term392 A _66640 lt2).
Proof. exact (eq_refl (term401 A _66640 lt2)). Qed.
Lemma lem5111165 {A : Type'} (y : type417 A) (lt2 : type1402 A) : (y lt2) = (y lt2).
Proof. exact (eq_refl (y lt2)). Qed.
Lemma lem5111166 {A : Type'} (_66640 : type418 A) (y : type417 A) (lt2 : type1402 A) : (term409 A _66640 y lt2) = (term410 A _66640 y lt2).
Proof. exact (MK_COMB (@lem5111164 A _66640 lt2) (@lem5111165 A y lt2)). Qed.
Lemma lem5111167 {A : Type'} (_66640 : type418 A) (y : type417 A) (lt2 : type1402 A) : (term410 A _66640 y lt2) = (term411 A _66640 y lt2).
Proof. exact (eq_refl (term410 A _66640 y lt2)). Qed.
Lemma lem5111168 {A : Type'} (_66640 : type418 A) (y : type417 A) (lt2 : type1402 A) : (term409 A _66640 y lt2) = (term411 A _66640 y lt2).
Proof. exact (TRANS (@lem5111166 A _66640 y lt2) (@lem5111167 A _66640 y lt2)). Qed.
Lemma lem5111169 {A : Type'} (_66640 : type418 A) (y : type417 A) : (term412 A _66640 y) = (term413 A _66640 y).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem5111168 A _66640 y lt2)). Qed.
Lemma lem5111170 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem5111171 {A : Type'} (_66640 : type418 A) (y : type417 A) : (term414 A _66640 y) = (term415 A _66640 y).
Proof. exact (MK_COMB (@lem5111170 A) (@lem5111169 A _66640 y)). Qed.
Lemma lem5111172 {A : Type'} (_66640 : type418 A) : (term416 A _66640) = (term417 A _66640).
Proof. exact (fun_ext (fun y : type417 A => @lem5111171 A _66640 y)). Qed.
Lemma lem5111173 {A : Type'} : (@ex ((A -> A -> Prop) -> A -> A -> A)) = (@ex ((A -> A -> Prop) -> A -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> A -> A -> A))). Qed.
Lemma lem5111174 {A : Type'} (_66640 : type418 A) : (term399 A _66640) = (term418 A _66640).
Proof. exact (MK_COMB (@lem5111173 A) (@lem5111172 A _66640)). Qed.
Lemma lem5111175 {A : Type'} (_66640 : type418 A) : ((term398 A _66640) = (term399 A _66640)) = ((term395 A _66640) = (term418 A _66640)).
Proof. exact (MK_COMB (@lem5111163 A _66640) (@lem5111174 A _66640)). Qed.
Lemma lem5111176 {A : Type'} (_66640 : type418 A) : (term395 A _66640) = (term418 A _66640).
Proof. exact (EQ_MP (@lem5111175 A _66640) (@lem5111150 A _66640)). Qed.
Lemma lem5111177 {A : Type'} (_66640 : type418 A) : (term326 A _66640) = (term418 A _66640).
Proof. exact (TRANS (@lem5111146 A _66640) (@lem5111176 A _66640)). Qed.
Lemma lem5111178 {A : Type'} (_66640 : type418 A) : (term323 A _66640) = (term323 A _66640).
Proof. exact (eq_refl (term323 A _66640)). Qed.
Lemma lem5111179 {A : Type'} (_66640 : type418 A) : (term327 A _66640) = (term419 A _66640).
Proof. exact (MK_COMB (@lem5111178 A _66640) (@lem5111177 A _66640)). Qed.
Lemma lem5111181 {A : Type'} (P : Prop) (Q : A -> Prop) : (term420 A P Q) = (term421 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5111182 {A : Type'} (P : Prop) (Q : type83 A) : (term422 A P Q) = (term423 A P Q).
Proof. exact (@lem5111181 (type417 A) P Q). Qed.
Lemma lem5111183 {A : Type'} (_66640 : type418 A) : (term424 A _66640) = (term425 A _66640).
Proof. exact (@lem5111182 A (term321 A _66640) (term417 A _66640)). Qed.
Lemma lem5111184 {A : Type'} (_66640 : type418 A) (y : type417 A) : (term426 A _66640 y) = (term415 A _66640 y).
Proof. exact (eq_refl (term426 A _66640 y)). Qed.
Lemma lem5111185 {A : Type'} (_66640 : type418 A) : (term427 A _66640) = (term417 A _66640).
Proof. exact (fun_ext (fun y : type417 A => @lem5111184 A _66640 y)). Qed.
Lemma lem5111186 {A : Type'} : (@ex ((A -> A -> Prop) -> A -> A -> A)) = (@ex ((A -> A -> Prop) -> A -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> A -> A -> A))). Qed.
Lemma lem5111187 {A : Type'} (_66640 : type418 A) : (term428 A _66640) = (term418 A _66640).
Proof. exact (MK_COMB (@lem5111186 A) (@lem5111185 A _66640)). Qed.
Lemma lem5111188 {A : Type'} (_66640 : type418 A) : (term323 A _66640) = (term323 A _66640).
Proof. exact (eq_refl (term323 A _66640)). Qed.
Lemma lem5111189 {A : Type'} (_66640 : type418 A) : (term424 A _66640) = (term419 A _66640).
Proof. exact (MK_COMB (@lem5111188 A _66640) (@lem5111187 A _66640)). Qed.
Lemma lem5111190 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5111191 {A : Type'} (_66640 : type418 A) : (term429 A _66640) = (term430 A _66640).
Proof. exact (MK_COMB (@lem5111190) (@lem5111189 A _66640)). Qed.
Lemma lem5111192 {A : Type'} (_66640 : type418 A) (y : type417 A) : (term426 A _66640 y) = (term415 A _66640 y).
Proof. exact (eq_refl (term426 A _66640 y)). Qed.
Lemma lem5111193 {A : Type'} (_66640 : type418 A) : (term323 A _66640) = (term323 A _66640).
Proof. exact (eq_refl (term323 A _66640)). Qed.
Lemma lem5111194 {A : Type'} (_66640 : type418 A) (y : type417 A) : (term431 A _66640 y) = (term432 A _66640 y).
Proof. exact (MK_COMB (@lem5111193 A _66640) (@lem5111192 A _66640 y)). Qed.
Lemma lem5111195 {A : Type'} (_66640 : type418 A) : (term433 A _66640) = (term434 A _66640).
Proof. exact (fun_ext (fun y : type417 A => @lem5111194 A _66640 y)). Qed.
Lemma lem5111196 {A : Type'} : (@ex ((A -> A -> Prop) -> A -> A -> A)) = (@ex ((A -> A -> Prop) -> A -> A -> A)).
Proof. exact (eq_refl (@ex ((A -> A -> Prop) -> A -> A -> A))). Qed.
Lemma lem5111197 {A : Type'} (_66640 : type418 A) : (term425 A _66640) = (term435 A _66640).
Proof. exact (MK_COMB (@lem5111196 A) (@lem5111195 A _66640)). Qed.
Lemma lem5111198 {A : Type'} (_66640 : type418 A) : ((term424 A _66640) = (term425 A _66640)) = ((term419 A _66640) = (term435 A _66640)).
Proof. exact (MK_COMB (@lem5111191 A _66640) (@lem5111197 A _66640)). Qed.
Lemma lem5111199 {A : Type'} (_66640 : type418 A) : (term419 A _66640) = (term435 A _66640).
Proof. exact (EQ_MP (@lem5111198 A _66640) (@lem5111183 A _66640)). Qed.
Lemma lem5111200 {A : Type'} (_66640 : type418 A) : (term327 A _66640) = (term435 A _66640).
Proof. exact (TRANS (@lem5111179 A _66640) (@lem5111199 A _66640)). Qed.
Lemma lem5111201 {A : Type'} (_66640 : type418 A) : (term259 A _66640) = (term435 A _66640).
Proof. exact (TRANS (@lem5111055 A _66640) (@lem5111200 A _66640)). Qed.
Lemma lem5111202 {A : Type'} (_66640 : type418 A) : (term228 A _66640) = (term435 A _66640).
Proof. exact (TRANS (@lem5110622 A _66640) (@lem5111201 A _66640)). Qed.
Lemma lem5111203 {A : Type'} (_66640 : type418 A) (h1 : term228 A _66640) : term435 A _66640.
Proof. exact (EQ_MP (@lem5111202 A _66640) (@lem5110577 A _66640 h1)). Qed.
Lemma lem5111332 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term104 A lt2 n s m) = (term695 A lt2 n s m).
Proof. exact (@lem17265 (Peano.lt m n) (term69 A lt2 n s m)). Qed.
Lemma lem5111333 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term106 A lt2 s m) = (term696 A lt2 s m).
Proof. exact (fun_ext (fun n : nat => @lem5111332 A lt2 n s m)). Qed.
Lemma lem5111334 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5111335 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term108 A lt2 s m) = (term697 A lt2 s m).
Proof. exact (MK_COMB (@lem5111334) (@lem5111333 A lt2 s m)). Qed.
Lemma lem5111336 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term110 A lt2 s) = (term698 A lt2 s).
Proof. exact (fun_ext (fun m : nat => @lem5111335 A lt2 s m)). Qed.
Lemma lem5111337 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5111394 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term62 A lt2 s) = (term699 A lt2 s).
Proof. exact (MK_COMB (@lem5111337) (@lem5111336 A lt2 s)). Qed.
Lemma lem5111395 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term699 A lt2 s.
Proof. exact (EQ_MP (@lem5111394 A lt2 s) (@lem5110582 A lt2 s h1)). Qed.
Lemma lem5111405 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term1020 A x _66640 lt2 s) : term1020 A x _66640 lt2 s.
Proof. exact (h1). Qed.
Lemma lem5111416 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term978 A lt2 x s) = (term1056 A lt2 x s).
Proof. exact (@lem17160 ((term563 A s x) = (term887 A s)) (term974 A lt2 x s)). Qed.
Lemma lem5111417 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term978 A lt2 x s) : term1056 A lt2 x s.
Proof. exact (EQ_MP (@lem5111416 A lt2 x s) (@lem5110584 A lt2 x s h1)). Qed.
Lemma lem5111418 (n : nat) : (term1012 n) = (term1012 n).
Proof. exact (eq_refl (term1012 n)). Qed.
Lemma lem5111419 : term1013 = term1013.
Proof. exact (fun_ext (fun n : nat => @lem5111418 n)). Qed.
Lemma lem5111420 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5111429 : term985 = term985.
Proof. exact (MK_COMB (@lem5111420) (@lem5111419)). Qed.
Lemma lem5111430 (h1 : term985) : term985.
Proof. exact (EQ_MP (@lem5111429) (@lem5110585 h1)). Qed.
Lemma lem5111603 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem5111608 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111609 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5111608 nat A f x). Qed.
Lemma lem5111611 {A : Type'} (s : nat -> A) (n : nat) : (s n) = (@I (nat -> A) s n).
Proof. exact (@lem5111609 A s n). Qed.
Lemma lem5111616 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111617 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5111616 nat A f x). Qed.
Lemma lem5111619 {A : Type'} (s : nat -> A) (m : nat) : (s m) = (@I (nat -> A) s m).
Proof. exact (@lem5111617 A s m). Qed.
Lemma lem5111620 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term575 A lt2 s n) = (term576 A lt2 s n).
Proof. exact (MK_COMB (@lem5111603 A lt2) (@lem5111611 A s n)). Qed.
Lemma lem5111621 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term69 A lt2 n s m) = (term577 A lt2 n s m).
Proof. exact (MK_COMB (@lem5111620 A lt2 s n) (@lem5111619 A s m)). Qed.
Lemma lem5111623 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111624 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5111623 A (A -> Prop) f x). Qed.
Lemma lem5111625 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (n : nat) : (term576 A lt2 s n) = (term578 A lt2 s n).
Proof. exact (@lem5111624 A lt2 (@I (nat -> A) s n)). Qed.
Lemma lem5111626 {A : Type'} (s : nat -> A) (m : nat) : (@I (nat -> A) s m) = (@I (nat -> A) s m).
Proof. exact (eq_refl (@I (nat -> A) s m)). Qed.
Lemma lem5111627 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term577 A lt2 n s m) = (term579 A lt2 n s m).
Proof. exact (MK_COMB (@lem5111625 A lt2 s n) (@lem5111626 A s m)). Qed.
Lemma lem5111629 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111630 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5111629 A Prop f x). Qed.
Lemma lem5111631 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term579 A lt2 n s m) = (term580 A lt2 n s m).
Proof. exact (@lem5111630 A (term578 A lt2 s n) (@I (nat -> A) s m)). Qed.
Lemma lem5111632 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term577 A lt2 n s m) = (term580 A lt2 n s m).
Proof. exact (TRANS (@lem5111627 A lt2 n s m) (@lem5111631 A lt2 n s m)). Qed.
Lemma lem5111633 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term69 A lt2 n s m) = (term580 A lt2 n s m).
Proof. exact (TRANS (@lem5111621 A lt2 n s m) (@lem5111632 A lt2 n s m)). Qed.
Lemma lem5111634 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5111641 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111642 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem5111641 nat (nat -> Prop) f x). Qed.
Lemma lem5111643 (m : nat) : (Peano.lt m) = (@I (nat -> nat -> Prop) Peano.lt m).
Proof. exact (@lem5111642 Peano.lt m). Qed.
Lemma lem5111644 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem5111645 (m : nat) (n : nat) : (Peano.lt m n) = (@I (nat -> nat -> Prop) Peano.lt m n).
Proof. exact (MK_COMB (@lem5111643 m) (@lem5111644 n)). Qed.
Lemma lem5111647 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111648 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem5111647 nat Prop f x). Qed.
Lemma lem5111649 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.lt m n) = (term719 m n).
Proof. exact (@lem5111648 (@I (nat -> nat -> Prop) Peano.lt m) n). Qed.
Lemma lem5111651 (m : nat) (n : nat) : (Peano.lt m n) = (term719 m n).
Proof. exact (TRANS (@lem5111645 m n) (@lem5111649 m n)). Qed.
Lemma lem5111652 (m : nat) (n : nat) : (term720 m n) = (term721 m n).
Proof. exact (MK_COMB (@lem5111634) (@lem5111651 m n)). Qed.
Lemma lem5111653 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5111654 (m : nat) (n : nat) : (term722 m n) = (term723 m n).
Proof. exact (MK_COMB (@lem5111653) (@lem5111652 m n)). Qed.
Lemma lem5111655 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term695 A lt2 n s m) = (term724 A lt2 n s m).
Proof. exact (MK_COMB (@lem5111654 m n) (@lem5111633 A lt2 n s m)). Qed.
Lemma lem5111656 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term696 A lt2 s m) = (term725 A lt2 s m).
Proof. exact (fun_ext (fun n : nat => @lem5111655 A lt2 n s m)). Qed.
Lemma lem5111657 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5111658 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term697 A lt2 s m) = (term726 A lt2 s m).
Proof. exact (MK_COMB (@lem5111657) (@lem5111656 A lt2 s m)). Qed.
Lemma lem5111659 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term698 A lt2 s) = (term727 A lt2 s).
Proof. exact (fun_ext (fun m : nat => @lem5111658 A lt2 s m)). Qed.
Lemma lem5111660 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5111661 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term699 A lt2 s) = (term728 A lt2 s).
Proof. exact (MK_COMB (@lem5111660) (@lem5111659 A lt2 s)). Qed.
Lemma lem5111662 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term728 A lt2 s.
Proof. exact (EQ_MP (@lem5111661 A lt2 s) (@lem5111395 A lt2 s h1)). Qed.
Lemma lem5111663 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem5111668 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111669 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5111668 nat A f x). Qed.
Lemma lem5111671 {A : Type'} (s : nat -> A) (x : nat) : (s x) = (@I (nat -> A) s x).
Proof. exact (@lem5111669 A s x). Qed.
Lemma lem5111672 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem5111675 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5111680 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111681 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5111680 nat nat f x). Qed.
Lemma lem5111683 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem5111681 NUMERAL 0). Qed.
Lemma lem5111684 {A : Type'} (s : nat -> A) : (term887 A s) = (term1057 A s).
Proof. exact (MK_COMB (@lem5111675 A s) (@lem5111683)). Qed.
Lemma lem5111686 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111687 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5111686 nat A f x). Qed.
Lemma lem5111688 {A : Type'} (s : nat -> A) : (term1057 A s) = (term1058 A s).
Proof. exact (@lem5111687 A s (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem5111689 {A : Type'} (s : nat -> A) : (term887 A s) = (term1058 A s).
Proof. exact (TRANS (@lem5111684 A s) (@lem5111688 A s)). Qed.
Lemma lem5111690 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (_66640 lt2) = (_66640 lt2).
Proof. exact (eq_refl (_66640 lt2)). Qed.
Lemma lem5111691 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term1014 A _66640 lt2 s) = (term1059 A _66640 lt2 s).
Proof. exact (MK_COMB (@lem5111690 A _66640 lt2) (@lem5111689 A s)). Qed.
Lemma lem5111693 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111694 {A : Type'} (f : type418 A) (x : type1402 A) : (f x) = (@I ((A -> A -> Prop) -> A -> A -> Prop) f x).
Proof. exact (@lem5111693 (type1402 A) (type1402 A) f x). Qed.
Lemma lem5111695 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) : (_66640 lt2) = (@I ((A -> A -> Prop) -> A -> A -> Prop) _66640 lt2).
Proof. exact (@lem5111694 A _66640 lt2). Qed.
Lemma lem5111696 {A : Type'} (s : nat -> A) : (term1058 A s) = (term1058 A s).
Proof. exact (eq_refl (term1058 A s)). Qed.
Lemma lem5111697 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term1059 A _66640 lt2 s) = (term1060 A _66640 lt2 s).
Proof. exact (MK_COMB (@lem5111695 A _66640 lt2) (@lem5111696 A s)). Qed.
Lemma lem5111699 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111700 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5111699 A (A -> Prop) f x). Qed.
Lemma lem5111701 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term1060 A _66640 lt2 s) = (term1061 A _66640 lt2 s).
Proof. exact (@lem5111700 A (@I ((A -> A -> Prop) -> A -> A -> Prop) _66640 lt2) (term1058 A s)). Qed.
Lemma lem5111702 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term1059 A _66640 lt2 s) = (term1061 A _66640 lt2 s).
Proof. exact (TRANS (@lem5111697 A _66640 lt2 s) (@lem5111701 A _66640 lt2 s)). Qed.
Lemma lem5111703 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term1014 A _66640 lt2 s) = (term1061 A _66640 lt2 s).
Proof. exact (TRANS (@lem5111691 A _66640 lt2 s) (@lem5111702 A _66640 lt2 s)). Qed.
Lemma lem5111704 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term1015 A _66640 lt2 s) = (term1062 A _66640 lt2 s).
Proof. exact (MK_COMB (@lem5111672 A) (@lem5111703 A _66640 lt2 s)). Qed.
Lemma lem5111706 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111707 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem5111706 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem5111708 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term1062 A _66640 lt2 s) = (term1063 A _66640 lt2 s).
Proof. exact (@lem5111707 A (@GSPEC A) (term1061 A _66640 lt2 s)). Qed.
Lemma lem5111709 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term1015 A _66640 lt2 s) = (term1063 A _66640 lt2 s).
Proof. exact (TRANS (@lem5111704 A _66640 lt2 s) (@lem5111708 A _66640 lt2 s)). Qed.
Lemma lem5111710 {A : Type'} (s : nat -> A) (x : nat) : (term1016 A s x) = (term1064 A s x).
Proof. exact (MK_COMB (@lem5111663 A) (@lem5111671 A s x)). Qed.
Lemma lem5111711 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term1018 A x _66640 lt2 s) = (term1065 A x _66640 lt2 s).
Proof. exact (MK_COMB (@lem5111710 A s x) (@lem5111709 A _66640 lt2 s)). Qed.
Lemma lem5111713 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111714 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem5111713 A (type686 A) f x). Qed.
Lemma lem5111715 {A : Type'} (s : nat -> A) (x : nat) : (term1064 A s x) = (term1066 A s x).
Proof. exact (@lem5111714 A (@IN A) (@I (nat -> A) s x)). Qed.
Lemma lem5111716 {A : Type'} (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term1063 A _66640 lt2 s) = (term1063 A _66640 lt2 s).
Proof. exact (eq_refl (term1063 A _66640 lt2 s)). Qed.
Lemma lem5111717 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term1065 A x _66640 lt2 s) = (term1067 A x _66640 lt2 s).
Proof. exact (MK_COMB (@lem5111715 A s x) (@lem5111716 A _66640 lt2 s)). Qed.
Lemma lem5111719 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111720 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem5111719 (A -> Prop) Prop f x). Qed.
Lemma lem5111721 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term1067 A x _66640 lt2 s) = (term1068 A x _66640 lt2 s).
Proof. exact (@lem5111720 A (term1066 A s x) (term1063 A _66640 lt2 s)). Qed.
Lemma lem5111722 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term1065 A x _66640 lt2 s) = (term1068 A x _66640 lt2 s).
Proof. exact (TRANS (@lem5111717 A x _66640 lt2 s) (@lem5111721 A x _66640 lt2 s)). Qed.
Lemma lem5111723 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term1018 A x _66640 lt2 s) = (term1068 A x _66640 lt2 s).
Proof. exact (TRANS (@lem5111711 A x _66640 lt2 s) (@lem5111722 A x _66640 lt2 s)). Qed.
Lemma lem5111724 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5111729 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111730 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5111729 nat A f x). Qed.
Lemma lem5111732 {A : Type'} (s : nat -> A) (x : nat) : (s x) = (@I (nat -> A) s x).
Proof. exact (@lem5111730 A s x). Qed.
Lemma lem5111733 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5111738 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111739 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5111738 nat nat f x). Qed.
Lemma lem5111741 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem5111739 NUMERAL 0). Qed.
Lemma lem5111742 {A : Type'} (s : nat -> A) : (term887 A s) = (term1057 A s).
Proof. exact (MK_COMB (@lem5111733 A s) (@lem5111741)). Qed.
Lemma lem5111744 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111745 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5111744 nat A f x). Qed.
Lemma lem5111746 {A : Type'} (s : nat -> A) : (term1057 A s) = (term1058 A s).
Proof. exact (@lem5111745 A s (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem5111747 {A : Type'} (s : nat -> A) : (term887 A s) = (term1058 A s).
Proof. exact (TRANS (@lem5111742 A s) (@lem5111746 A s)). Qed.
Lemma lem5111748 {A : Type'} (s : nat -> A) (x : nat) : (term739 A s x) = (term740 A s x).
Proof. exact (MK_COMB (@lem5111724 A) (@lem5111732 A s x)). Qed.
Lemma lem5111749 {A : Type'} (x : nat) (s : nat -> A) : ((s x) = (term887 A s)) = ((@I (nat -> A) s x) = (term1058 A s)).
Proof. exact (MK_COMB (@lem5111748 A s x) (@lem5111747 A s)). Qed.
Lemma lem5111750 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5111751 {A : Type'} (x : nat) (s : nat -> A) : (term1019 A x s) = (term1069 A x s).
Proof. exact (MK_COMB (@lem5111750) (@lem5111749 A x s)). Qed.
Lemma lem5111752 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) : (term1020 A x _66640 lt2 s) = (term1070 A x _66640 lt2 s).
Proof. exact (MK_COMB (@lem5111751 A x s) (@lem5111723 A x _66640 lt2 s)). Qed.
Lemma lem5111753 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term1020 A x _66640 lt2 s) : term1070 A x _66640 lt2 s.
Proof. exact (EQ_MP (@lem5111752 A x _66640 lt2 s) (@lem5111405 A x _66640 lt2 s h1)). Qed.
Lemma lem5111754 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5111755 {A : Type'} (lt2 : type1402 A) : lt2 = lt2.
Proof. exact (eq_refl lt2). Qed.
Lemma lem5111756 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5111761 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111762 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5111761 nat nat f x). Qed.
Lemma lem5111764 (x : nat) : (S x) = (@I (nat -> nat) S x).
Proof. exact (@lem5111762 S x). Qed.
Lemma lem5111765 {A : Type'} (s : nat -> A) (x : nat) : (term563 A s x) = (term564 A s x).
Proof. exact (MK_COMB (@lem5111756 A s) (@lem5111764 x)). Qed.
Lemma lem5111767 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111768 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5111767 nat A f x). Qed.
Lemma lem5111769 {A : Type'} (s : nat -> A) (x : nat) : (term564 A s x) = (term565 A s x).
Proof. exact (@lem5111768 A s (@I (nat -> nat) S x)). Qed.
Lemma lem5111770 {A : Type'} (s : nat -> A) (x : nat) : (term563 A s x) = (term565 A s x).
Proof. exact (TRANS (@lem5111765 A s x) (@lem5111769 A s x)). Qed.
Lemma lem5111771 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5111776 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111777 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5111776 nat nat f x). Qed.
Lemma lem5111779 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem5111777 NUMERAL 0). Qed.
Lemma lem5111780 {A : Type'} (s : nat -> A) : (term887 A s) = (term1057 A s).
Proof. exact (MK_COMB (@lem5111771 A s) (@lem5111779)). Qed.
Lemma lem5111782 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111783 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5111782 nat A f x). Qed.
Lemma lem5111784 {A : Type'} (s : nat -> A) : (term1057 A s) = (term1058 A s).
Proof. exact (@lem5111783 A s (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem5111785 {A : Type'} (s : nat -> A) : (term887 A s) = (term1058 A s).
Proof. exact (TRANS (@lem5111780 A s) (@lem5111784 A s)). Qed.
Lemma lem5111786 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term566 A lt2 s x) = (term567 A lt2 s x).
Proof. exact (MK_COMB (@lem5111755 A lt2) (@lem5111770 A s x)). Qed.
Lemma lem5111787 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term974 A lt2 x s) = (term1071 A lt2 x s).
Proof. exact (MK_COMB (@lem5111786 A lt2 s x) (@lem5111785 A s)). Qed.
Lemma lem5111789 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111790 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem5111789 A (A -> Prop) f x). Qed.
Lemma lem5111791 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (x : nat) : (term567 A lt2 s x) = (term569 A lt2 s x).
Proof. exact (@lem5111790 A lt2 (term565 A s x)). Qed.
Lemma lem5111792 {A : Type'} (s : nat -> A) : (term1058 A s) = (term1058 A s).
Proof. exact (eq_refl (term1058 A s)). Qed.
Lemma lem5111793 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term1071 A lt2 x s) = (term1072 A lt2 x s).
Proof. exact (MK_COMB (@lem5111791 A lt2 s x) (@lem5111792 A s)). Qed.
Lemma lem5111795 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111796 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem5111795 A Prop f x). Qed.
Lemma lem5111797 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term1072 A lt2 x s) = (term1073 A lt2 x s).
Proof. exact (@lem5111796 A (term569 A lt2 s x) (term1058 A s)). Qed.
Lemma lem5111798 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term1071 A lt2 x s) = (term1073 A lt2 x s).
Proof. exact (TRANS (@lem5111793 A lt2 x s) (@lem5111797 A lt2 x s)). Qed.
Lemma lem5111799 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term974 A lt2 x s) = (term1073 A lt2 x s).
Proof. exact (TRANS (@lem5111787 A lt2 x s) (@lem5111798 A lt2 x s)). Qed.
Lemma lem5111800 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term1074 A lt2 x s) = (term1075 A lt2 x s).
Proof. exact (MK_COMB (@lem5111754) (@lem5111799 A lt2 x s)). Qed.
Lemma lem5111801 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5111802 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem5111803 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5111808 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111809 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5111808 nat nat f x). Qed.
Lemma lem5111811 (x : nat) : (S x) = (@I (nat -> nat) S x).
Proof. exact (@lem5111809 S x). Qed.
Lemma lem5111812 {A : Type'} (s : nat -> A) (x : nat) : (term563 A s x) = (term564 A s x).
Proof. exact (MK_COMB (@lem5111803 A s) (@lem5111811 x)). Qed.
Lemma lem5111814 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111815 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5111814 nat A f x). Qed.
Lemma lem5111816 {A : Type'} (s : nat -> A) (x : nat) : (term564 A s x) = (term565 A s x).
Proof. exact (@lem5111815 A s (@I (nat -> nat) S x)). Qed.
Lemma lem5111817 {A : Type'} (s : nat -> A) (x : nat) : (term563 A s x) = (term565 A s x).
Proof. exact (TRANS (@lem5111812 A s x) (@lem5111816 A s x)). Qed.
Lemma lem5111818 {A : Type'} (s : nat -> A) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5111823 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111824 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5111823 nat nat f x). Qed.
Lemma lem5111826 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem5111824 NUMERAL 0). Qed.
Lemma lem5111827 {A : Type'} (s : nat -> A) : (term887 A s) = (term1057 A s).
Proof. exact (MK_COMB (@lem5111818 A s) (@lem5111826)). Qed.
Lemma lem5111829 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111830 {A : Type'} (f : nat -> A) (x : nat) : (f x) = (@I (nat -> A) f x).
Proof. exact (@lem5111829 nat A f x). Qed.
Lemma lem5111831 {A : Type'} (s : nat -> A) : (term1057 A s) = (term1058 A s).
Proof. exact (@lem5111830 A s (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem5111832 {A : Type'} (s : nat -> A) : (term887 A s) = (term1058 A s).
Proof. exact (TRANS (@lem5111827 A s) (@lem5111831 A s)). Qed.
Lemma lem5111833 {A : Type'} (s : nat -> A) (x : nat) : (term1076 A s x) = (term1077 A s x).
Proof. exact (MK_COMB (@lem5111802 A) (@lem5111817 A s x)). Qed.
Lemma lem5111834 {A : Type'} (x : nat) (s : nat -> A) : ((term563 A s x) = (term887 A s)) = ((term565 A s x) = (term1058 A s)).
Proof. exact (MK_COMB (@lem5111833 A s x) (@lem5111832 A s)). Qed.
Lemma lem5111835 {A : Type'} (x : nat) (s : nat -> A) : (term1078 A x s) = (term1079 A x s).
Proof. exact (MK_COMB (@lem5111801) (@lem5111834 A x s)). Qed.
Lemma lem5111836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5111837 {A : Type'} (x : nat) (s : nat -> A) : (term1080 A x s) = (term1081 A x s).
Proof. exact (MK_COMB (@lem5111836) (@lem5111835 A x s)). Qed.
Lemma lem5111838 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term1056 A lt2 x s) = (term1082 A lt2 x s).
Proof. exact (MK_COMB (@lem5111837 A x s) (@lem5111800 A lt2 x s)). Qed.
Lemma lem5111839 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term978 A lt2 x s) : term1082 A lt2 x s.
Proof. exact (EQ_MP (@lem5111838 A lt2 x s) (@lem5111417 A lt2 x s h1)). Qed.
Lemma lem5111840 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem5111845 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111846 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5111845 nat nat f x). Qed.
Lemma lem5111848 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem5111846 NUMERAL 0). Qed.
Lemma lem5111853 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111854 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem5111853 nat nat f x). Qed.
Lemma lem5111856 (n : nat) : (S n) = (@I (nat -> nat) S n).
Proof. exact (@lem5111854 S n). Qed.
Lemma lem5111857 : term1083 = term1084.
Proof. exact (MK_COMB (@lem5111840) (@lem5111848)). Qed.
Lemma lem5111858 (n : nat) : (term1012 n) = (term1085 n).
Proof. exact (MK_COMB (@lem5111857) (@lem5111856 n)). Qed.
Lemma lem5111860 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111861 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem5111860 nat (nat -> Prop) f x). Qed.
Lemma lem5111862 : term1084 = term1086.
Proof. exact (@lem5111861 Peano.lt (@I (nat -> nat) NUMERAL 0)). Qed.
Lemma lem5111863 (n : nat) : (@I (nat -> nat) S n) = (@I (nat -> nat) S n).
Proof. exact (eq_refl (@I (nat -> nat) S n)). Qed.
Lemma lem5111864 (n : nat) : (term1085 n) = (term1087 n).
Proof. exact (MK_COMB (@lem5111862) (@lem5111863 n)). Qed.
Lemma lem5111866 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5111867 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem5111866 nat Prop f x). Qed.
Lemma lem5111868 (n : nat) : (term1087 n) = (term1088 n).
Proof. exact (@lem5111867 term1086 (@I (nat -> nat) S n)). Qed.
Lemma lem5111869 (n : nat) : (term1085 n) = (term1088 n).
Proof. exact (TRANS (@lem5111864 n) (@lem5111868 n)). Qed.
Lemma lem5111870 (n : nat) : (term1012 n) = (term1088 n).
Proof. exact (TRANS (@lem5111858 n) (@lem5111869 n)). Qed.
Lemma lem5111871 : term1013 = term1089.
Proof. exact (fun_ext (fun n : nat => @lem5111870 n)). Qed.
Lemma lem5111872 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5111873 : term985 = term1090.
Proof. exact (MK_COMB (@lem5111872) (@lem5111871)). Qed.
Lemma lem5111874 (h1 : term985) : term1090.
Proof. exact (EQ_MP (@lem5111873) (@lem5111430 h1)). Qed.
Lemma lem5112155 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term724 A lt2 n s m) = (term724 A lt2 n s m).
Proof. exact (eq_refl (term724 A lt2 n s m)). Qed.
Lemma lem5112156 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term725 A lt2 s m) = (term725 A lt2 s m).
Proof. exact (fun_ext (fun n : nat => @lem5112155 A lt2 n s m)). Qed.
Lemma lem5112157 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5112158 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term726 A lt2 s m) = (term726 A lt2 s m).
Proof. exact (MK_COMB (@lem5112157) (@lem5112156 A lt2 s m)). Qed.
Lemma lem5112159 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term727 A lt2 s) = (term727 A lt2 s).
Proof. exact (fun_ext (fun m : nat => @lem5112158 A lt2 s m)). Qed.
Lemma lem5112160 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5112162 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term728 A lt2 s) = (term728 A lt2 s).
Proof. exact (MK_COMB (@lem5112160) (@lem5112159 A lt2 s)). Qed.
Lemma lem5112163 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term728 A lt2 s.
Proof. exact (EQ_MP (@lem5112162 A lt2 s) (@lem5111662 A lt2 s h1)). Qed.
Lemma lem5112165 (n : nat) : (term1088 n) = (term1088 n).
Proof. exact (eq_refl (term1088 n)). Qed.
Lemma lem5112166 : term1089 = term1089.
Proof. exact (fun_ext (fun n : nat => @lem5112165 n)). Qed.
Lemma lem5112167 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5112169 : term1090 = term1090.
Proof. exact (MK_COMB (@lem5112167) (@lem5112166)). Qed.
Lemma lem5112170 (h1 : term985) : term1090.
Proof. exact (EQ_MP (@lem5112169) (@lem5111874 h1)). Qed.
Lemma lem5112305 {A : Type'} (lt2 : type1402 A) (n : nat) (s : nat -> A) (m : nat) : (term724 A lt2 n s m) = (term724 A lt2 n s m).
Proof. exact (eq_refl (term724 A lt2 n s m)). Qed.
Lemma lem5112306 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term725 A lt2 s m) = (term725 A lt2 s m).
Proof. exact (fun_ext (fun n : nat => @lem5112305 A lt2 n s m)). Qed.
Lemma lem5112307 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5112308 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (m : nat) : (term726 A lt2 s m) = (term726 A lt2 s m).
Proof. exact (MK_COMB (@lem5112307) (@lem5112306 A lt2 s m)). Qed.
Lemma lem5112309 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term727 A lt2 s) = (term727 A lt2 s).
Proof. exact (fun_ext (fun m : nat => @lem5112308 A lt2 s m)). Qed.
Lemma lem5112310 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5112312 {A : Type'} (lt2 : type1402 A) (s : nat -> A) : (term728 A lt2 s) = (term728 A lt2 s).
Proof. exact (MK_COMB (@lem5112310) (@lem5112309 A lt2 s)). Qed.
Lemma lem5112313 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term728 A lt2 s.
Proof. exact (EQ_MP (@lem5112312 A lt2 s) (@lem5111662 A lt2 s h1)). Qed.
Lemma lem5112315 (n : nat) : (term1088 n) = (term1088 n).
Proof. exact (eq_refl (term1088 n)). Qed.
Lemma lem5112316 : term1089 = term1089.
Proof. exact (fun_ext (fun n : nat => @lem5112315 n)). Qed.
Lemma lem5112317 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5112319 : term1090 = term1090.
Proof. exact (MK_COMB (@lem5112317) (@lem5112316)). Qed.
Lemma lem5112320 (h1 : term985) : term1090.
Proof. exact (EQ_MP (@lem5112319) (@lem5111874 h1)). Qed.
Lemma lem5112420 {A : Type'} (_66647 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term745 A lt2 s _66647.
Proof. exact (@lem5112163 A lt2 s h1 _66647). Qed.
Lemma lem5112421 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66647 : nat) : (term745 A lt2 s _66647) = (term726 A lt2 s _66647).
Proof. exact (eq_refl (term745 A lt2 s _66647)). Qed.
Lemma lem5112422 {A : Type'} (_66647 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term726 A lt2 s _66647.
Proof. exact (EQ_MP (@lem5112421 A lt2 s _66647) (@lem5112420 A _66647 lt2 s h1)). Qed.
Lemma lem5112423 {A : Type'} (_66647 : nat) (_66648 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term746 A lt2 s _66647 _66648.
Proof. exact (@lem5112422 A _66647 lt2 s h1 _66648). Qed.
Lemma lem5112424 {A : Type'} (lt2 : type1402 A) (_66648 : nat) (s : nat -> A) (_66647 : nat) : (term746 A lt2 s _66647 _66648) = (term724 A lt2 _66648 s _66647).
Proof. exact (eq_refl (term746 A lt2 s _66647 _66648)). Qed.
Lemma lem5112426 (_66649 : nat) (h1 : term985) : term1091 _66649.
Proof. exact (@lem5112170 h1 _66649). Qed.
Lemma lem5112427 (_66649 : nat) : (term1091 _66649) = (term1088 _66649).
Proof. exact (eq_refl (term1091 _66649)). Qed.
Lemma lem5112468 {A : Type'} (_66663 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term745 A lt2 s _66663.
Proof. exact (@lem5112313 A lt2 s h1 _66663). Qed.
Lemma lem5112469 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66663 : nat) : (term745 A lt2 s _66663) = (term726 A lt2 s _66663).
Proof. exact (eq_refl (term745 A lt2 s _66663)). Qed.
Lemma lem5112470 {A : Type'} (_66663 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term726 A lt2 s _66663.
Proof. exact (EQ_MP (@lem5112469 A lt2 s _66663) (@lem5112468 A _66663 lt2 s h1)). Qed.
Lemma lem5112471 {A : Type'} (_66663 : nat) (_66664 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term746 A lt2 s _66663 _66664.
Proof. exact (@lem5112470 A _66663 lt2 s h1 _66664). Qed.
Lemma lem5112472 {A : Type'} (lt2 : type1402 A) (_66664 : nat) (s : nat -> A) (_66663 : nat) : (term746 A lt2 s _66663 _66664) = (term724 A lt2 _66664 s _66663).
Proof. exact (eq_refl (term746 A lt2 s _66663 _66664)). Qed.
Lemma lem5112474 (_66665 : nat) (h1 : term985) : term1091 _66665.
Proof. exact (@lem5112320 h1 _66665). Qed.
Lemma lem5112475 (_66665 : nat) : (term1091 _66665) = (term1088 _66665).
Proof. exact (eq_refl (term1091 _66665)). Qed.
Lemma lem5112521 {A : Type'} (_66648 : nat) (_66647 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term724 A lt2 _66648 s _66647.
Proof. exact (EQ_MP (@lem5112424 A lt2 _66648 s _66647) (@lem5112423 A _66647 _66648 lt2 s h1)). Qed.
Lemma lem5112539 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term978 A lt2 x s) : term1075 A lt2 x s.
Proof. exact (proj2 (@lem5111839 A lt2 x s h1)). Qed.
Lemma lem5112565 {A : Type'} (_66664 : nat) (_66663 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term724 A lt2 _66664 s _66663.
Proof. exact (EQ_MP (@lem5112472 A lt2 _66664 s _66663) (@lem5112471 A _66663 _66664 lt2 s h1)). Qed.
Lemma lem5112583 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term978 A lt2 x s) : term1075 A lt2 x s.
Proof. exact (proj2 (@lem5111839 A lt2 x s h1)). Qed.
Lemma lem5112856 (_66649 : nat) (h1 : term985) : term1088 _66649.
Proof. exact (EQ_MP (@lem5112427 _66649) (@lem5112426 _66649 h1)). Qed.
Lemma lem5112857 (x : nat) (h1 : term985) : term1088 x.
Proof. exact (@lem5112856 x h1). Qed.
Lemma lem5112858 (x : nat) (h1 : term985) : term1092 x.
Proof. exact (fun h0 : term1093 x => @lem5112857 x h1). Qed.
Lemma lem5112860 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5112861 (x : nat) : (term1092 x) = (term1088 x).
Proof. exact (@lem5112860 (term1088 x)). Qed.
Lemma lem5112862 (x : nat) (h1 : term985) : term1088 x.
Proof. exact (EQ_MP (@lem5112861 x) (@lem5112858 x h1)). Qed.
Lemma lem5112868 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5112869 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66647 : nat) (_66648 : nat) : (term724 A lt2 _66648 s _66647) = (term840 A lt2 s _66647 _66648).
Proof. exact (@lem5112868 (term580 A lt2 _66648 s _66647) (term721 _66647 _66648)). Qed.
Lemma lem5112875 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5112876 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66647 : nat) (_66648 : nat) : (term841 A lt2 _66648 s _66647) = (term842 A lt2 s _66647 _66648).
Proof. exact (MK_COMB (@lem5112875) (@lem5112869 A lt2 s _66647 _66648)). Qed.
Lemma lem5112882 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66647 : nat) (_66648 : nat) : (term840 A lt2 s _66647 _66648) = (term840 A lt2 s _66647 _66648).
Proof. exact (eq_refl (term840 A lt2 s _66647 _66648)). Qed.
Lemma lem5112883 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66647 : nat) (_66648 : nat) : ((term724 A lt2 _66648 s _66647) = (term840 A lt2 s _66647 _66648)) = ((term840 A lt2 s _66647 _66648) = (term840 A lt2 s _66647 _66648)).
Proof. exact (MK_COMB (@lem5112876 A lt2 s _66647 _66648) (@lem5112882 A lt2 s _66647 _66648)). Qed.
Lemma lem5112885 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5112886 (x : Prop) : (x = x) = True.
Proof. exact (@lem5112885 Prop x). Qed.
Lemma lem5112887 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66647 : nat) (_66648 : nat) : ((term840 A lt2 s _66647 _66648) = (term840 A lt2 s _66647 _66648)) = True.
Proof. exact (@lem5112886 (term840 A lt2 s _66647 _66648)). Qed.
Lemma lem5112888 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66647 : nat) (_66648 : nat) : ((term724 A lt2 _66648 s _66647) = (term840 A lt2 s _66647 _66648)) = True.
Proof. exact (TRANS (@lem5112883 A lt2 s _66647 _66648) (@lem5112887 A lt2 s _66647 _66648)). Qed.
Lemma lem5112889 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66647 : nat) (_66648 : nat) : True = ((term724 A lt2 _66648 s _66647) = (term840 A lt2 s _66647 _66648)).
Proof. exact (SYM (@lem5112888 A lt2 s _66647 _66648)). Qed.
Lemma lem5112890 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66647 : nat) (_66648 : nat) : (term724 A lt2 _66648 s _66647) = (term840 A lt2 s _66647 _66648).
Proof. exact (EQ_MP (@lem5112889 A lt2 s _66647 _66648) (@lem0)). Qed.
Lemma lem5112891 {A : Type'} (_66647 : nat) (_66648 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term840 A lt2 s _66647 _66648.
Proof. exact (EQ_MP (@lem5112890 A lt2 s _66647 _66648) (@lem5112521 A _66648 _66647 lt2 s h1)). Qed.
Lemma lem5112893 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5112894 {A : Type'} (lt2 : type1402 A) (_66648 : nat) (s : nat -> A) (_66647 : nat) : (term840 A lt2 s _66647 _66648) = (term843 A lt2 _66648 s _66647).
Proof. exact (@lem5112893 (term721 _66647 _66648) (term580 A lt2 _66648 s _66647)). Qed.
Lemma lem5112896 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5112897 (_66647 : nat) (_66648 : nat) : (term844 _66647 _66648) = (term719 _66647 _66648).
Proof. exact (@lem5112896 (term719 _66647 _66648)). Qed.
Lemma lem5112898 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5112899 (_66647 : nat) (_66648 : nat) : (term845 _66647 _66648) = (term846 _66647 _66648).
Proof. exact (MK_COMB (@lem5112898) (@lem5112897 _66647 _66648)). Qed.
Lemma lem5112900 {A : Type'} (lt2 : type1402 A) (_66648 : nat) (s : nat -> A) (_66647 : nat) : (term580 A lt2 _66648 s _66647) = (term580 A lt2 _66648 s _66647).
Proof. exact (eq_refl (term580 A lt2 _66648 s _66647)). Qed.
Lemma lem5112901 {A : Type'} (lt2 : type1402 A) (_66648 : nat) (s : nat -> A) (_66647 : nat) : (term843 A lt2 _66648 s _66647) = (term847 A lt2 _66648 s _66647).
Proof. exact (MK_COMB (@lem5112899 _66647 _66648) (@lem5112900 A lt2 _66648 s _66647)). Qed.
Lemma lem5112902 {A : Type'} (lt2 : type1402 A) (_66648 : nat) (s : nat -> A) (_66647 : nat) : (term840 A lt2 s _66647 _66648) = (term847 A lt2 _66648 s _66647).
Proof. exact (TRANS (@lem5112894 A lt2 _66648 s _66647) (@lem5112901 A lt2 _66648 s _66647)). Qed.
Lemma lem5112905 {A : Type'} (_66648 : nat) (_66647 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term847 A lt2 _66648 s _66647.
Proof. exact (EQ_MP (@lem5112902 A lt2 _66648 s _66647) (@lem5112891 A _66647 _66648 lt2 s h1)). Qed.
Lemma lem5112906 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term1094 A lt2 x s.
Proof. exact (@lem5112905 A (@I (nat -> nat) S x) (@I (nat -> nat) NUMERAL 0) lt2 s h1). Qed.
Lemma lem5112909 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) (h2 : term985) : term1073 A lt2 x s.
Proof. exact (@lem5112906 A x lt2 s h1 (@lem5112862 x h2)). Qed.
Lemma lem5112910 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) (h2 : term985) : term1095 A lt2 x s.
Proof. exact (fun h0 : term1075 A lt2 x s => @lem5112909 A x lt2 s h1 h2). Qed.
Lemma lem5112912 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5112913 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term1095 A lt2 x s) = (term1073 A lt2 x s).
Proof. exact (@lem5112912 (term1073 A lt2 x s)). Qed.
Lemma lem5112914 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) (h2 : term985) : term1073 A lt2 x s.
Proof. exact (EQ_MP (@lem5112913 A lt2 x s) (@lem5112910 A x lt2 s h1 h2)). Qed.
Lemma lem5112917 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5112919 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term1075 A lt2 x s) = (term1096 A lt2 x s).
Proof. exact (@lem5112917 (term1073 A lt2 x s)). Qed.
Lemma lem5112922 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term978 A lt2 x s) : term1096 A lt2 x s.
Proof. exact (EQ_MP (@lem5112919 A lt2 x s) (@lem5112539 A lt2 x s h1)). Qed.
Lemma lem5112925 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term62 A lt2 s) (h2 : term985) (h3 : term978 A lt2 x s) : False.
Proof. exact (@lem5112922 A lt2 x s h3 (@lem5112914 A x lt2 s h1 h2)). Qed.
Lemma lem5112926 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term62 A lt2 s) (h2 : term985) (h3 : term978 A lt2 x s) : term619.
Proof. exact (fun h0 : ~ False => @lem5112925 A lt2 x s h1 h2 h3). Qed.
Lemma lem5112928 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5112929 : term619 = False.
Proof. exact (@lem5112928 False). Qed.
Lemma lem5112930 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term62 A lt2 s) (h2 : term985) (h3 : term978 A lt2 x s) : False.
Proof. exact (EQ_MP (@lem5112929) (@lem5112926 A lt2 x s h1 h2 h3)). Qed.
Lemma lem5113218 (_66665 : nat) (h1 : term985) : term1088 _66665.
Proof. exact (EQ_MP (@lem5112475 _66665) (@lem5112474 _66665 h1)). Qed.
Lemma lem5113219 (x : nat) (h1 : term985) : term1088 x.
Proof. exact (@lem5113218 x h1). Qed.
Lemma lem5113220 (x : nat) (h1 : term985) : term1092 x.
Proof. exact (fun h0 : term1093 x => @lem5113219 x h1). Qed.
Lemma lem5113222 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5113223 (x : nat) : (term1092 x) = (term1088 x).
Proof. exact (@lem5113222 (term1088 x)). Qed.
Lemma lem5113224 (x : nat) (h1 : term985) : term1088 x.
Proof. exact (EQ_MP (@lem5113223 x) (@lem5113220 x h1)). Qed.
Lemma lem5113230 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5113231 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66663 : nat) (_66664 : nat) : (term724 A lt2 _66664 s _66663) = (term840 A lt2 s _66663 _66664).
Proof. exact (@lem5113230 (term580 A lt2 _66664 s _66663) (term721 _66663 _66664)). Qed.
Lemma lem5113237 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5113238 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66663 : nat) (_66664 : nat) : (term841 A lt2 _66664 s _66663) = (term842 A lt2 s _66663 _66664).
Proof. exact (MK_COMB (@lem5113237) (@lem5113231 A lt2 s _66663 _66664)). Qed.
Lemma lem5113244 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66663 : nat) (_66664 : nat) : (term840 A lt2 s _66663 _66664) = (term840 A lt2 s _66663 _66664).
Proof. exact (eq_refl (term840 A lt2 s _66663 _66664)). Qed.
Lemma lem5113245 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66663 : nat) (_66664 : nat) : ((term724 A lt2 _66664 s _66663) = (term840 A lt2 s _66663 _66664)) = ((term840 A lt2 s _66663 _66664) = (term840 A lt2 s _66663 _66664)).
Proof. exact (MK_COMB (@lem5113238 A lt2 s _66663 _66664) (@lem5113244 A lt2 s _66663 _66664)). Qed.
Lemma lem5113247 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5113248 (x : Prop) : (x = x) = True.
Proof. exact (@lem5113247 Prop x). Qed.
Lemma lem5113249 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66663 : nat) (_66664 : nat) : ((term840 A lt2 s _66663 _66664) = (term840 A lt2 s _66663 _66664)) = True.
Proof. exact (@lem5113248 (term840 A lt2 s _66663 _66664)). Qed.
Lemma lem5113250 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66663 : nat) (_66664 : nat) : ((term724 A lt2 _66664 s _66663) = (term840 A lt2 s _66663 _66664)) = True.
Proof. exact (TRANS (@lem5113245 A lt2 s _66663 _66664) (@lem5113249 A lt2 s _66663 _66664)). Qed.
Lemma lem5113251 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66663 : nat) (_66664 : nat) : True = ((term724 A lt2 _66664 s _66663) = (term840 A lt2 s _66663 _66664)).
Proof. exact (SYM (@lem5113250 A lt2 s _66663 _66664)). Qed.
Lemma lem5113252 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (_66663 : nat) (_66664 : nat) : (term724 A lt2 _66664 s _66663) = (term840 A lt2 s _66663 _66664).
Proof. exact (EQ_MP (@lem5113251 A lt2 s _66663 _66664) (@lem0)). Qed.
Lemma lem5113253 {A : Type'} (_66663 : nat) (_66664 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term840 A lt2 s _66663 _66664.
Proof. exact (EQ_MP (@lem5113252 A lt2 s _66663 _66664) (@lem5112565 A _66664 _66663 lt2 s h1)). Qed.
Lemma lem5113255 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5113256 {A : Type'} (lt2 : type1402 A) (_66664 : nat) (s : nat -> A) (_66663 : nat) : (term840 A lt2 s _66663 _66664) = (term843 A lt2 _66664 s _66663).
Proof. exact (@lem5113255 (term721 _66663 _66664) (term580 A lt2 _66664 s _66663)). Qed.
Lemma lem5113258 (a : Prop) : (term121 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5113259 (_66663 : nat) (_66664 : nat) : (term844 _66663 _66664) = (term719 _66663 _66664).
Proof. exact (@lem5113258 (term719 _66663 _66664)). Qed.
Lemma lem5113260 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5113261 (_66663 : nat) (_66664 : nat) : (term845 _66663 _66664) = (term846 _66663 _66664).
Proof. exact (MK_COMB (@lem5113260) (@lem5113259 _66663 _66664)). Qed.
Lemma lem5113262 {A : Type'} (lt2 : type1402 A) (_66664 : nat) (s : nat -> A) (_66663 : nat) : (term580 A lt2 _66664 s _66663) = (term580 A lt2 _66664 s _66663).
Proof. exact (eq_refl (term580 A lt2 _66664 s _66663)). Qed.
Lemma lem5113263 {A : Type'} (lt2 : type1402 A) (_66664 : nat) (s : nat -> A) (_66663 : nat) : (term843 A lt2 _66664 s _66663) = (term847 A lt2 _66664 s _66663).
Proof. exact (MK_COMB (@lem5113261 _66663 _66664) (@lem5113262 A lt2 _66664 s _66663)). Qed.
Lemma lem5113264 {A : Type'} (lt2 : type1402 A) (_66664 : nat) (s : nat -> A) (_66663 : nat) : (term840 A lt2 s _66663 _66664) = (term847 A lt2 _66664 s _66663).
Proof. exact (TRANS (@lem5113256 A lt2 _66664 s _66663) (@lem5113263 A lt2 _66664 s _66663)). Qed.
Lemma lem5113267 {A : Type'} (_66664 : nat) (_66663 : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term847 A lt2 _66664 s _66663.
Proof. exact (EQ_MP (@lem5113264 A lt2 _66664 s _66663) (@lem5113253 A _66663 _66664 lt2 s h1)). Qed.
Lemma lem5113268 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) : term1094 A lt2 x s.
Proof. exact (@lem5113267 A (@I (nat -> nat) S x) (@I (nat -> nat) NUMERAL 0) lt2 s h1). Qed.
Lemma lem5113271 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) (h2 : term985) : term1073 A lt2 x s.
Proof. exact (@lem5113268 A x lt2 s h1 (@lem5113224 x h2)). Qed.
Lemma lem5113272 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) (h2 : term985) : term1095 A lt2 x s.
Proof. exact (fun h0 : term1075 A lt2 x s => @lem5113271 A x lt2 s h1 h2). Qed.
Lemma lem5113274 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5113275 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term1095 A lt2 x s) = (term1073 A lt2 x s).
Proof. exact (@lem5113274 (term1073 A lt2 x s)). Qed.
Lemma lem5113276 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) (h2 : term985) : term1073 A lt2 x s.
Proof. exact (EQ_MP (@lem5113275 A lt2 x s) (@lem5113272 A x lt2 s h1 h2)). Qed.
Lemma lem5113279 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5113281 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term1075 A lt2 x s) = (term1096 A lt2 x s).
Proof. exact (@lem5113279 (term1073 A lt2 x s)). Qed.
Lemma lem5113284 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term978 A lt2 x s) : term1096 A lt2 x s.
Proof. exact (EQ_MP (@lem5113281 A lt2 x s) (@lem5112583 A lt2 x s h1)). Qed.
Lemma lem5113287 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term62 A lt2 s) (h2 : term985) (h3 : term978 A lt2 x s) : False.
Proof. exact (@lem5113284 A lt2 x s h3 (@lem5113276 A x lt2 s h1 h2)). Qed.
Lemma lem5113288 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term62 A lt2 s) (h2 : term985) (h3 : term978 A lt2 x s) : term619.
Proof. exact (fun h0 : ~ False => @lem5113287 A lt2 x s h1 h2 h3). Qed.
Lemma lem5113290 (p : Prop) : (term596 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5113291 : term619 = False.
Proof. exact (@lem5113290 False). Qed.
Lemma lem5113292 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (h1 : term62 A lt2 s) (h2 : term985) (h3 : term978 A lt2 x s) : False.
Proof. exact (EQ_MP (@lem5113291) (@lem5113288 A lt2 x s h1 h2 h3)). Qed.
Lemma lem5113293 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term62 A lt2 s) (h2 : term985) (h3 : term978 A lt2 x s) (h4 : term1020 A x _66640 lt2 s) : False.
Proof. exact (or_elim (@lem5111753 A x _66640 lt2 s h4) (fun h0 : (@I (nat -> A) s x) = (term1058 A s) => @lem5112930 A lt2 x s h1 h2 h3) (fun h0 : term1068 A x _66640 lt2 s => @lem5113292 A lt2 x s h1 h2 h3)). Qed.
Lemma lem5113294 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term228 A _66640) (h2 : term62 A lt2 s) (h3 : term985) (h4 : term978 A lt2 x s) (h5 : term1020 A x _66640 lt2 s) : False.
Proof. exact (ex_elim (@lem5111203 A _66640 h1) (fun y : type417 A => fun h0 : term434 A _66640 y => @lem5113293 A x _66640 lt2 s h2 h3 h4 h5)). Qed.
Lemma lem5113295 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term228 A _66640) (h2 : term62 A lt2 s) (h3 : term985) (h4 : term978 A lt2 x s) (h5 : term1020 A x _66640 lt2 s) : term985 = False.
Proof. exact (prop_ext (fun h6 : term985 => @lem5113294 A x _66640 lt2 s h1 h2 h3 h4 h5) (fun h6 : False => @lem5111430 h3)). Qed.
Lemma lem5113296 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term228 A _66640) (h2 : term62 A lt2 s) (h3 : term985) (h4 : term978 A lt2 x s) (h5 : term1020 A x _66640 lt2 s) : False.
Proof. exact (EQ_MP (@lem5113295 A x _66640 lt2 s h1 h2 h3 h4 h5) (@lem5111430 h3)). Qed.
Lemma lem5113297 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term228 A _66640) (h2 : term62 A lt2 s) (h3 : term985) (h4 : term978 A lt2 x s) (h5 : term1020 A x _66640 lt2 s) : (term1020 A x _66640 lt2 s) = False.
Proof. exact (prop_ext (fun h6 : term1020 A x _66640 lt2 s => @lem5113296 A x _66640 lt2 s h1 h2 h3 h4 h5) (fun h6 : False => @lem5111405 A x _66640 lt2 s h5)). Qed.
Lemma lem5113298 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term228 A _66640) (h2 : term62 A lt2 s) (h3 : term985) (h4 : term978 A lt2 x s) (h5 : term1020 A x _66640 lt2 s) : False.
Proof. exact (EQ_MP (@lem5113297 A x _66640 lt2 s h1 h2 h3 h4 h5) (@lem5111405 A x _66640 lt2 s h5)). Qed.
Lemma lem5113299 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term228 A _66640) (h2 : term62 A lt2 s) (h3 : term978 A lt2 x s) (h4 : term1020 A x _66640 lt2 s) : term983.
Proof. exact (fun h0 : term985 => @lem5113298 A x _66640 lt2 s h1 h2 h0 h3 h4). Qed.
Lemma lem5113300 : term983 = term984.
Proof. exact (@lem69 term985). Qed.
Lemma lem5113301 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term228 A _66640) (h2 : term62 A lt2 s) (h3 : term978 A lt2 x s) (h4 : term1020 A x _66640 lt2 s) : term984.
Proof. exact (EQ_MP (@lem5113300) (@lem5113299 A x _66640 lt2 s h1 h2 h3 h4)). Qed.
Lemma lem5113302 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term228 A _66640) (h2 : term62 A lt2 s) (h3 : term1020 A x _66640 lt2 s) : term988 A lt2 x s.
Proof. exact (fun h0 : term978 A lt2 x s => @lem5113301 A x _66640 lt2 s h1 h2 h0 h3). Qed.
Lemma lem5113303 {A : Type'} (x : nat) (_66640 : type418 A) (lt2 : type1402 A) (s : nat -> A) (h1 : term228 A _66640) (h2 : term62 A lt2 s) : term1022 A _66640 lt2 x s.
Proof. exact (fun h0 : term1020 A x _66640 lt2 s => @lem5113302 A x _66640 lt2 s h1 h2 h0). Qed.
Lemma lem5113304 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (_66640 : type418 A) (h1 : term228 A _66640) : term1023 A _66640 lt2 x s.
Proof. exact (fun h0 : term62 A lt2 s => @lem5113303 A x _66640 lt2 s h1 h0). Qed.
Lemma lem5113305 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (_66640 : type418 A) (h1 : term228 A _66640) : term1024 A _66640 lt2 x s.
Proof. exact (fun h0 : term61 A lt2 s => @lem5113304 A lt2 x s _66640 h1). Qed.
Lemma lem5113306 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (_66640 : type418 A) (h1 : term228 A _66640) : term1025 A _66640 lt2 x s.
Proof. exact (fun h0 : term154 A _66640 lt2 => @lem5113305 A lt2 x s _66640 h1). Qed.
Lemma lem5113307 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (_66640 : type418 A) (h1 : term228 A _66640) : term1026 A _66640 lt2 x s.
Proof. exact (fun h0 : term58 A lt2 => @lem5113306 A lt2 x s _66640 h1). Qed.
Lemma lem5113308 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) (_66640 : type418 A) (h1 : term228 A _66640) : term1027 A _66640 lt2 x s.
Proof. exact (fun h0 : term56 A lt2 => @lem5113307 A lt2 x s _66640 h1). Qed.
Lemma lem5113313 {A : Type'} (x : nat) (s : nat -> A) (_66640 : type418 A) (h1 : term228 A _66640) : term1029 A _66640 x s.
Proof. exact (fun lt2 : type1402 A => @lem5113308 A lt2 x s _66640 h1). Qed.
Lemma lem5113318 {A : Type'} (s : nat -> A) (_66640 : type418 A) (h1 : term228 A _66640) : term1031 A _66640 s.
Proof. exact (fun x : nat => @lem5113313 A x s _66640 h1). Qed.
Lemma lem5113323 {A : Type'} (_66640 : type418 A) (h1 : term228 A _66640) : term1033 A _66640.
Proof. exact (fun s : nat -> A => @lem5113318 A s _66640 h1). Qed.
Lemma lem5113324 {A : Type'} (_66640 : type418 A) : term1053 A _66640.
Proof. exact (fun h0 : term228 A _66640 => @lem5113323 A _66640 h0). Qed.
Lemma lem5113329 {A : Type'} : term1055 A.
Proof. exact (fun _66640 : type418 A => @lem5113324 A _66640). Qed.
Lemma lem5113330 {A : Type'} : term1010 A.
Proof. exact (EQ_MP (@lem5110576 A) (@lem5113329 A)). Qed.
Lemma lem5113331 {A : Type'} (s : nat -> A) : term1097 A s.
Proof. exact (@lem5113330 A s). Qed.
Lemma lem5113332 {A : Type'} (s : nat -> A) : (term1097 A s) = (term1006 A s).
Proof. exact (eq_refl (term1097 A s)). Qed.
Lemma lem5113333 {A : Type'} (s : nat -> A) : term1006 A s.
Proof. exact (EQ_MP (@lem5113332 A s) (@lem5113331 A s)). Qed.
Lemma lem5113334 {A : Type'} (s : nat -> A) (x : nat) : term1098 A s x.
Proof. exact (@lem5113333 A s x). Qed.
Lemma lem5113335 {A : Type'} (x : nat) (s : nat -> A) : (term1098 A s x) = (term1002 A x s).
Proof. exact (eq_refl (term1098 A s x)). Qed.
Lemma lem5113336 {A : Type'} (x : nat) (s : nat -> A) : term1002 A x s.
Proof. exact (EQ_MP (@lem5113335 A x s) (@lem5113334 A s x)). Qed.
Lemma lem5113337 {A : Type'} (x : nat) (s : nat -> A) (lt2 : type1402 A) : term1099 A x s lt2.
Proof. exact (@lem5113336 A x s lt2). Qed.
Lemma lem5113338 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : (term1099 A x s lt2) = (term979 A lt2 x s).
Proof. exact (eq_refl (term1099 A x s lt2)). Qed.
Lemma lem5113339 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : term979 A lt2 x s.
Proof. exact (EQ_MP (@lem5113338 A lt2 x s) (@lem5113337 A x s lt2)). Qed.
Lemma lem5113341 {A : Type'} (lt2 : type1402 A) (x : nat) (s : nat -> A) : term979 A lt2 x s.
Proof. exact (@lem5109887 A lt2 x s (@lem5113339 A lt2 x s)). Qed.
Lemma lem5113342 {A : Type'} (x : nat) (s : nat -> A) (lt2 : type1402 A) (h1 : term56 A lt2) : term997 A lt2 x s.
Proof. exact (@lem5113341 A lt2 x s (@lem5103242 A lt2 h1)). Qed.
Lemma lem5113343 {A : Type'} (x : nat) (s : nat -> A) (lt2 : type1402 A) (h1 : term58 A lt2) (h2 : term56 A lt2) : term995 A lt2 x s.
Proof. exact (@lem5113342 A x s lt2 h2 (@lem5103244 A lt2 h1)). Qed.
Lemma lem5113344 {A : Type'} (x : nat) (s : nat -> A) (lt2 : type1402 A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) : term993 A lt2 x s.
Proof. exact (@lem5113343 A x s lt2 h1 h3 (@lem5103243 A lt2 h2)). Qed.
Lemma lem5113345 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term61 A lt2 s) : term991 A lt2 x s.
Proof. exact (@lem5113344 A x s lt2 h1 h2 h3 (@lem5103258 A lt2 s h4)). Qed.
Lemma lem5113346 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term989 A lt2 x s.
Proof. exact (@lem5113345 A x lt2 s h1 h2 h3 h5 (@lem5103259 A lt2 s h4)). Qed.
Lemma lem5113347 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) (h6 : term917 A x lt2 s) : term987 A lt2 x s.
Proof. exact (@lem5113346 A x lt2 s h1 h2 h3 h4 h5 (@lem5109798 A x lt2 s h6)). Qed.
Lemma lem5113348 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) (h6 : term978 A lt2 x s) (h7 : term917 A x lt2 s) : term983.
Proof. exact (@lem5113347 A x lt2 s h1 h2 h3 h4 h5 h7 (@lem5109871 A lt2 x s h6)). Qed.
Lemma lem5113349 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) (h6 : term978 A lt2 x s) (h7 : term917 A x lt2 s) : False.
Proof. exact (@lem5113348 A x lt2 s h1 h2 h3 h4 h5 h6 h7 (@lem91530)). Qed.
Lemma lem5113350 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) (h6 : term978 A lt2 x s) (h7 : term917 A x lt2 s) : (term978 A lt2 x s) = False.
Proof. exact (prop_ext (fun h8 : term978 A lt2 x s => @lem5113349 A x lt2 s h1 h2 h3 h4 h5 h6 h7) (fun h8 : False => @lem5109871 A lt2 x s h6)). Qed.
Lemma lem5113351 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) (h6 : term978 A lt2 x s) (h7 : term917 A x lt2 s) : False.
Proof. exact (EQ_MP (@lem5113350 A x lt2 s h1 h2 h3 h4 h5 h6 h7) (@lem5109871 A lt2 x s h6)). Qed.
Lemma lem5113352 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) (h6 : term917 A x lt2 s) : term977 A lt2 x s.
Proof. exact (fun h0 : term978 A lt2 x s => @lem5113351 A x lt2 s h1 h2 h3 h4 h5 h0 h6). Qed.
Lemma lem5113353 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) (h6 : term917 A x lt2 s) : term976 A lt2 x s.
Proof. exact (EQ_MP (@lem5109870 A lt2 x s) (@lem5113352 A x lt2 s h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5113354 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) (h6 : term917 A x lt2 s) : term931 A x lt2 s.
Proof. exact (EQ_MP (@lem5109866 A x lt2 s) (@lem5113353 A x lt2 s h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem5113355 {A : Type'} (x : nat) (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term933 A x lt2 s.
Proof. exact (fun h0 : term917 A x lt2 s => @lem5113354 A x lt2 s h1 h2 h3 h4 h5 h0). Qed.
Lemma lem5113360 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term937 A lt2 s.
Proof. exact (fun x : nat => @lem5113355 A x lt2 s h1 h2 h3 h4 h5). Qed.
Lemma lem5113361 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term939 A lt2 s.
Proof. exact (conj (@lem5109835 A lt2 s) (@lem5113360 A lt2 s h1 h2 h3 h4 h5)). Qed.
Lemma lem5113362 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term920 A lt2 s.
Proof. exact (@lem5109797 A lt2 s (@lem5113361 A lt2 s h1 h2 h3 h4 h5)). Qed.
Lemma lem5113363 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term890 A lt2 s.
Proof. exact (EQ_MP (@lem5109774 A lt2 s) (@lem5113362 A lt2 s h1 h2 h3 h4 h5)). Qed.
Lemma lem5113364 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term891 A lt2 s.
Proof. exact (EQ_MP (@lem5109704 A s lt2 h2) (@lem5113363 A lt2 s h1 h2 h3 h4 h5)). Qed.
Lemma lem5113365 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term1100 A s.
Proof. exact (ex_intro (term1101 A s) (term894 A lt2 s) (@lem5113364 A lt2 s h1 h2 h3 h4 h5)). Qed.
Lemma lem5113366 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term878 A s.
Proof. exact (@lem5109632 A s (@lem5113365 A lt2 s h1 h2 h3 h4 h5)). Qed.
Lemma lem5113367 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term875 A s.
Proof. exact (EQ_MP (@lem5109628 A s) (@lem5113366 A lt2 s h1 h2 h3 h4 h5)). Qed.
Lemma lem5113368 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term870 A s.
Proof. exact (EQ_MP (@lem5109617 A s) (@lem5113367 A lt2 s h1 h2 h3 h4 h5)). Qed.
Lemma lem5113369 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term627 A s) (h5 : term62 A lt2 s) (h6 : term61 A lt2 s) : False.
Proof. exact (@lem5113368 A lt2 s h1 h2 h3 h5 h6 (@lem5109598 A s h4)). Qed.
Lemma lem5113370 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term1102 A s.
Proof. exact (fun h0 : term627 A s => @lem5113369 A lt2 s h1 h2 h3 h0 h4 h5). Qed.
Lemma lem5113371 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term1103 A s.
Proof. exact (conj (@lem5109594 A lt2 s h1 h2 h3 h4 h5) (@lem5113370 A lt2 s h1 h2 h3 h4 h5)). Qed.
Lemma lem5113372 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : term1104 A s.
Proof. exact (@lem5106065 A s (@lem5113371 A lt2 s h1 h2 h3 h4 h5)). Qed.
Lemma lem5113373 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : False.
Proof. exact (@lem5113372 A lt2 s h1 h2 h3 h4 h5 (@lem5103213 A s)). Qed.
Lemma lem5113374 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : (term62 A lt2 s) = False.
Proof. exact (prop_ext (fun h6 : term62 A lt2 s => @lem5113373 A lt2 s h1 h2 h3 h4 h5) (fun h6 : False => @lem5103259 A lt2 s h4)). Qed.
Lemma lem5113375 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term62 A lt2 s) (h5 : term61 A lt2 s) : False.
Proof. exact (EQ_MP (@lem5113374 A lt2 s h1 h2 h3 h4 h5) (@lem5103259 A lt2 s h4)). Qed.
Lemma lem5113376 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term61 A lt2 s) : (term62 A lt2 s) = False.
Proof. exact (prop_ext (fun h5 : term62 A lt2 s => @lem5113375 A lt2 s h1 h2 h3 h5 h4) (fun h5 : False => @lem5106062 A lt2 s h1 h2 h3 h4)). Qed.
Lemma lem5113377 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term61 A lt2 s) : False.
Proof. exact (EQ_MP (@lem5113376 A lt2 s h1 h2 h3 h4) (@lem5106062 A lt2 s h1 h2 h3 h4)). Qed.
Lemma lem5113378 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term61 A lt2 s) : (term61 A lt2 s) = False.
Proof. exact (prop_ext (fun h5 : term61 A lt2 s => @lem5113377 A lt2 s h1 h2 h3 h4) (fun h5 : False => @lem5103258 A lt2 s h4)). Qed.
Lemma lem5113379 {A : Type'} (lt2 : type1402 A) (s : nat -> A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term61 A lt2 s) : False.
Proof. exact (EQ_MP (@lem5113378 A lt2 s h1 h2 h3 h4) (@lem5103258 A lt2 s h4)). Qed.
Lemma lem5113380 {A : Type'} (lt2 : type1402 A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) (h4 : term60 A lt2) : False.
Proof. exact (ex_elim (@lem5103257 A lt2 h4) (fun s : nat -> A => fun h0 : term1105 A lt2 s => @lem5113379 A lt2 s h1 h2 h3 h0)). Qed.
Lemma lem5113381 {A : Type'} (lt2 : type1402 A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) : term1106 A lt2.
Proof. exact (fun h0 : term60 A lt2 => @lem5113380 A lt2 h1 h2 h3 h0). Qed.
Lemma lem5113382 {A : Type'} (lt2 : type1402 A) : (term1106 A lt2) = (term59 A lt2).
Proof. exact (@lem69 (term60 A lt2)). Qed.
Lemma lem5113383 {A : Type'} (lt2 : type1402 A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) : term59 A lt2.
Proof. exact (EQ_MP (@lem5113382 A lt2) (@lem5113381 A lt2 h1 h2 h3)). Qed.
Lemma lem5113384 {A : Type'} (lt2 : type1402 A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) : @WF A lt2.
Proof. exact (EQ_MP (@lem5103256 A lt2) (@lem5113383 A lt2 h1 h2 h3)). Qed.
Lemma lem5113385 {A : Type'} (lt2 : type1402 A) (h1 : term54 A lt2) : term55 A lt2.
Proof. exact (proj2 (@lem5103240 A lt2 h1)). Qed.
Lemma lem5113386 {A : Type'} (lt2 : type1402 A) (h1 : term54 A lt2) : term56 A lt2.
Proof. exact (proj1 (@lem5103240 A lt2 h1)). Qed.
Lemma lem5113387 {A : Type'} (lt2 : type1402 A) (h1 : term55 A lt2) : term57 A lt2.
Proof. exact (proj2 (@lem5103241 A lt2 h1)). Qed.
Lemma lem5113388 {A : Type'} (lt2 : type1402 A) (h1 : term55 A lt2) : term58 A lt2.
Proof. exact (proj1 (@lem5103241 A lt2 h1)). Qed.
Lemma lem5113389 {A : Type'} (lt2 : type1402 A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) : (term57 A lt2) = (@WF A lt2).
Proof. exact (prop_ext (fun h4 : term57 A lt2 => @lem5113384 A lt2 h1 h2 h3) (fun h4 : @WF A lt2 => @lem5103243 A lt2 h2)). Qed.
Lemma lem5113390 {A : Type'} (lt2 : type1402 A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) : @WF A lt2.
Proof. exact (EQ_MP (@lem5113389 A lt2 h1 h2 h3) (@lem5103243 A lt2 h2)). Qed.
Lemma lem5113391 {A : Type'} (lt2 : type1402 A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) : (term58 A lt2) = (@WF A lt2).
Proof. exact (prop_ext (fun h4 : term58 A lt2 => @lem5113390 A lt2 h1 h2 h3) (fun h4 : @WF A lt2 => @lem5103244 A lt2 h1)). Qed.
Lemma lem5113392 {A : Type'} (lt2 : type1402 A) (h1 : term58 A lt2) (h2 : term57 A lt2) (h3 : term56 A lt2) : @WF A lt2.
Proof. exact (EQ_MP (@lem5113391 A lt2 h1 h2 h3) (@lem5103244 A lt2 h1)). Qed.
Lemma lem5113393 {A : Type'} (lt2 : type1402 A) (h1 : term58 A lt2) (h2 : term56 A lt2) (h3 : term55 A lt2) : (term57 A lt2) = (@WF A lt2).
Proof. exact (prop_ext (fun h4 : term57 A lt2 => @lem5113392 A lt2 h1 h4 h2) (fun h4 : @WF A lt2 => @lem5113387 A lt2 h3)). Qed.
Lemma lem5113394 {A : Type'} (lt2 : type1402 A) (h1 : term58 A lt2) (h2 : term56 A lt2) (h3 : term55 A lt2) : @WF A lt2.
Proof. exact (EQ_MP (@lem5113393 A lt2 h1 h2 h3) (@lem5113387 A lt2 h3)). Qed.
Lemma lem5113395 {A : Type'} (lt2 : type1402 A) (h1 : term56 A lt2) (h2 : term55 A lt2) : (term58 A lt2) = (@WF A lt2).
Proof. exact (prop_ext (fun h3 : term58 A lt2 => @lem5113394 A lt2 h3 h1 h2) (fun h3 : @WF A lt2 => @lem5113388 A lt2 h2)). Qed.
Lemma lem5113396 {A : Type'} (lt2 : type1402 A) (h1 : term56 A lt2) (h2 : term55 A lt2) : @WF A lt2.
Proof. exact (EQ_MP (@lem5113395 A lt2 h1 h2) (@lem5113388 A lt2 h2)). Qed.
Lemma lem5113397 {A : Type'} (lt2 : type1402 A) (h1 : term56 A lt2) (h2 : term55 A lt2) : (term56 A lt2) = (@WF A lt2).
Proof. exact (prop_ext (fun h3 : term56 A lt2 => @lem5113396 A lt2 h1 h2) (fun h3 : @WF A lt2 => @lem5103242 A lt2 h1)). Qed.
Lemma lem5113398 {A : Type'} (lt2 : type1402 A) (h1 : term56 A lt2) (h2 : term55 A lt2) : @WF A lt2.
Proof. exact (EQ_MP (@lem5113397 A lt2 h1 h2) (@lem5103242 A lt2 h1)). Qed.
Lemma lem5113399 {A : Type'} (lt2 : type1402 A) (h1 : term56 A lt2) (h2 : term54 A lt2) : (term55 A lt2) = (@WF A lt2).
Proof. exact (prop_ext (fun h3 : term55 A lt2 => @lem5113398 A lt2 h1 h3) (fun h3 : @WF A lt2 => @lem5113385 A lt2 h2)). Qed.
Lemma lem5113400 {A : Type'} (lt2 : type1402 A) (h1 : term56 A lt2) (h2 : term54 A lt2) : @WF A lt2.
Proof. exact (EQ_MP (@lem5113399 A lt2 h1 h2) (@lem5113385 A lt2 h2)). Qed.
Lemma lem5113401 {A : Type'} (lt2 : type1402 A) (h1 : term54 A lt2) : (term56 A lt2) = (@WF A lt2).
Proof. exact (prop_ext (fun h2 : term56 A lt2 => @lem5113400 A lt2 h2 h1) (fun h2 : @WF A lt2 => @lem5113386 A lt2 h1)). Qed.
Lemma lem5113402 {A : Type'} (lt2 : type1402 A) (h1 : term54 A lt2) : @WF A lt2.
Proof. exact (EQ_MP (@lem5113401 A lt2 h1) (@lem5113386 A lt2 h1)). Qed.
Lemma lem5113403 {A : Type'} (lt2 : type1402 A) : term1107 A lt2.
Proof. exact (fun h0 : term54 A lt2 => @lem5113402 A lt2 h0). Qed.
Lemma lem5113408 {A : Type'} : term1108 A.
Proof. exact (fun lt2 : type1402 A => @lem5113403 A lt2). Qed.
