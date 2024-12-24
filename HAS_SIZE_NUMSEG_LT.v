Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_NUMSEG_LT_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import FINITE_EMPTY_spec.
Require Import FINITE_INSERT_spec.
Require Import HAS_SIZE_spec.
Require Import LT_REFL_spec.
Require Import NUMSEG_CLAUSES_LT_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem4621003 {_100044 : Type'} (s : _100044 -> Prop) : term0 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem4621004 {_100044 : Type'} (s : _100044 -> Prop) : (term0 _100044 s) = (term1 _100044 s).
Proof. exact (eq_refl (term0 _100044 s)). Qed.
Lemma lem4621005 {_100044 : Type'} (s : _100044 -> Prop) : term1 _100044 s.
Proof. exact (EQ_MP (@lem4621004 _100044 s) (@lem4621003 _100044 s)). Qed.
Lemma lem4621006 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term2 _100044 s n.
Proof. exact (@lem4621005 _100044 s n). Qed.
Lemma lem4621007 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term2 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term3 _100044 s n)).
Proof. exact (eq_refl (term2 _100044 s n)). Qed.
Lemma lem4621014 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term3 _100044 s n).
Proof. exact (EQ_MP (@lem4621007 _100044 s n) (@lem4621006 _100044 s n)). Qed.
Lemma lem4621015 (s : nat -> Prop) (n : nat) : (@HAS_SIZE nat s n) = (term4 s n).
Proof. exact (@lem4621014 nat s n). Qed.
Lemma lem4621016 (n : nat) : (term5 n) = (term6 n).
Proof. exact (@lem4621015 (term7 n) n). Qed.
Lemma lem4621029 : term8 = term9.
Proof. exact (fun_ext (fun n : nat => @lem4621016 n)). Qed.
Lemma lem4621030 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621031 : term10 = term11.
Proof. exact (MK_COMB (@lem4621030) (@lem4621029)). Qed.
Lemma lem4621036 : term11 = term10.
Proof. exact (SYM (@lem4621031)). Qed.
Lemma lem4621038 (P : nat -> Prop) : term12 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem4621039 : term13.
Proof. exact (@lem4621038 term9). Qed.
Lemma lem4621040 : term14 = term15.
Proof. exact (eq_refl term14). Qed.
Lemma lem4621041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4621042 : term16 = term17.
Proof. exact (MK_COMB (@lem4621041) (@lem4621040)). Qed.
Lemma lem4621043 (n : nat) : (term18 n) = (term6 n).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem4621044 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4621045 (n : nat) : (term19 n) = (term20 n).
Proof. exact (MK_COMB (@lem4621044) (@lem4621043 n)). Qed.
Lemma lem4621046 (n : nat) : (term21 n) = (term22 n).
Proof. exact (eq_refl (term21 n)). Qed.
Lemma lem4621047 (n : nat) : (term23 n) = (term24 n).
Proof. exact (MK_COMB (@lem4621045 n) (@lem4621046 n)). Qed.
Lemma lem4621048 : term25 = term26.
Proof. exact (fun_ext (fun n : nat => @lem4621047 n)). Qed.
Lemma lem4621049 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621050 : term27 = term28.
Proof. exact (MK_COMB (@lem4621049) (@lem4621048)). Qed.
Lemma lem4621051 : term29 = term30.
Proof. exact (MK_COMB (@lem4621042) (@lem4621050)). Qed.
Lemma lem4621052 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4621053 : term31 = term32.
Proof. exact (MK_COMB (@lem4621052) (@lem4621051)). Qed.
Lemma lem4621054 (n : nat) : (term18 n) = (term6 n).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem4621055 : term33 = term9.
Proof. exact (fun_ext (fun n : nat => @lem4621054 n)). Qed.
Lemma lem4621056 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621057 : term34 = term11.
Proof. exact (MK_COMB (@lem4621056) (@lem4621055)). Qed.
Lemma lem4621058 : term13 = term35.
Proof. exact (MK_COMB (@lem4621053) (@lem4621057)). Qed.
Lemma lem4621059 : term35.
Proof. exact (EQ_MP (@lem4621058) (@lem4621039)). Qed.
Lemma lem4621060 (n : nat) (h1 : term6 n) : term6 n.
Proof. exact (h1). Qed.
Lemma lem4621125 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem4621135 : term36 = (@EMPTY nat).
Proof. exact (proj1 (@lem4621002)). Qed.
Lemma lem4621136 : (@FINITE nat) = (@FINITE nat).
Proof. exact (eq_refl (@FINITE nat)). Qed.
Lemma lem4621137 : term37 = (@FINITE nat (@EMPTY nat)).
Proof. exact (MK_COMB (@lem4621136) (@lem4621135)). Qed.
Lemma lem4621139 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem4621125 _92140) (@lem3596285 _92140)). Qed.
Lemma lem4621140 : (@FINITE nat (@EMPTY nat)) = True.
Proof. exact (@lem4621139 nat). Qed.
Lemma lem4621141 : term37 = True.
Proof. exact (TRANS (@lem4621137) (@lem4621140)). Qed.
Lemma lem4621142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4621143 : term38 = (and True).
Proof. exact (MK_COMB (@lem4621142) (@lem4621141)). Qed.
Lemma lem4621147 : term36 = (@EMPTY nat).
Proof. exact (proj1 (@lem4621002)). Qed.
Lemma lem4621148 : (@CARD nat) = (@CARD nat).
Proof. exact (eq_refl (@CARD nat)). Qed.
Lemma lem4621149 : term39 = (@CARD nat (@EMPTY nat)).
Proof. exact (MK_COMB (@lem4621148) (@lem4621147)). Qed.
Lemma lem4621151 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4621152 : (@CARD nat (@EMPTY nat)) = (NUMERAL 0).
Proof. exact (@lem4621151 nat). Qed.
Lemma lem4621153 : term39 = (NUMERAL 0).
Proof. exact (TRANS (@lem4621149) (@lem4621152)). Qed.
Lemma lem4621154 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4621155 : term40 = term41.
Proof. exact (MK_COMB (@lem4621154) (@lem4621153)). Qed.
Lemma lem4621156 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem4621157 : (term39 = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem4621155) (@lem4621156)). Qed.
Lemma lem4621159 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4621160 (x : nat) : (x = x) = True.
Proof. exact (@lem4621159 nat x). Qed.
Lemma lem4621161 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem4621160 (NUMERAL 0)). Qed.
Lemma lem4621162 : (term39 = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem4621157) (@lem4621161)). Qed.
Lemma lem4621163 : term15 = (True /\ True).
Proof. exact (MK_COMB (@lem4621143) (@lem4621162)). Qed.
Lemma lem4621165 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4621166 : (True /\ True) = True.
Proof. exact (@lem4621165 True). Qed.
Lemma lem4621167 : term15 = True.
Proof. exact (TRANS (@lem4621163) (@lem4621166)). Qed.
Lemma lem4621168 : True = term15.
Proof. exact (SYM (@lem4621167)). Qed.
Lemma lem4621169 : term15.
Proof. exact (EQ_MP (@lem4621168) (@lem0)). Qed.
Lemma lem4621170 (n : nat) : term42 n.
Proof. exact (@lem91686 n). Qed.
Lemma lem4621171 (n : nat) : (term42 n) = (term43 n).
Proof. exact (eq_refl (term42 n)). Qed.
Lemma lem4621172 (n : nat) : term43 n.
Proof. exact (EQ_MP (@lem4621171 n) (@lem4621170 n)). Qed.
Lemma lem4621173 (n : nat) : term44 n.
Proof. exact (@lem82 (Peano.lt n n)). Qed.
Lemma lem4621199 {_83095 : Type'} : term45 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4621200 {_83095 : Type'} (p : _83095 -> Prop) : term46 _83095 p.
Proof. exact (@lem4621199 _83095 p). Qed.
Lemma lem4621201 {_83095 : Type'} (p : _83095 -> Prop) : (term46 _83095 p) = (term47 _83095 p).
Proof. exact (eq_refl (term46 _83095 p)). Qed.
Lemma lem4621202 {_83095 : Type'} (p : _83095 -> Prop) : term47 _83095 p.
Proof. exact (EQ_MP (@lem4621201 _83095 p) (@lem4621200 _83095 p)). Qed.
Lemma lem4621203 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term48 _83095 p x.
Proof. exact (@lem4621202 _83095 p x). Qed.
Lemma lem4621204 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term48 _83095 p x) = ((term49 _83095 x p) = (p x)).
Proof. exact (eq_refl (term48 _83095 p x)). Qed.
Lemma lem4621213 {A : Type'} (s : A -> Prop) : term50 A s.
Proof. exact (@lem3608316 A s). Qed.
Lemma lem4621214 {A : Type'} (s : A -> Prop) : (term50 A s) = (term51 A s).
Proof. exact (eq_refl (term50 A s)). Qed.
Lemma lem4621215 {A : Type'} (s : A -> Prop) : term51 A s.
Proof. exact (EQ_MP (@lem4621214 A s) (@lem4621213 A s)). Qed.
Lemma lem4621216 {A : Type'} (s : A -> Prop) (x : A) : term52 A s x.
Proof. exact (@lem4621215 A s x). Qed.
Lemma lem4621217 {A : Type'} (x : A) (s : A -> Prop) : (term52 A s x) = ((term53 A x s) = (@FINITE A s)).
Proof. exact (eq_refl (term52 A s x)). Qed.
Lemma lem4621219 {A : Type'} : term54 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem4621220 {A : Type'} (x : A) : term55 A x.
Proof. exact (@lem4621219 A x). Qed.
Lemma lem4621221 {A : Type'} (x : A) : (term55 A x) = (term56 A x).
Proof. exact (eq_refl (term55 A x)). Qed.
Lemma lem4621222 {A : Type'} (x : A) : term56 A x.
Proof. exact (EQ_MP (@lem4621221 A x) (@lem4621220 A x)). Qed.
Lemma lem4621223 {A : Type'} (x : A) (s : A -> Prop) : term57 A x s.
Proof. exact (@lem4621222 A x s). Qed.
Lemma lem4621224 {A : Type'} (x : A) (s : A -> Prop) : (term57 A x s) = (term58 A x s).
Proof. exact (eq_refl (term57 A x s)). Qed.
Lemma lem4621225 {A : Type'} (x : A) (s : A -> Prop) : term58 A x s.
Proof. exact (EQ_MP (@lem4621224 A x s) (@lem4621223 A x s)). Qed.
Lemma lem4621226 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4621227 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term59 A x s) = (term60 A x s).
Proof. exact (@lem4621225 A x s (@lem4621226 A s h1)). Qed.
Lemma lem4621236 : term61.
Proof. exact (proj2 (@lem4621002)). Qed.
Lemma lem4621237 (k : nat) : term62 k.
Proof. exact (@lem4621236 k). Qed.
Lemma lem4621238 (k : nat) : (term62 k) = ((term63 k) = (term64 k)).
Proof. exact (eq_refl (term62 k)). Qed.
Lemma lem4621242 (n : nat) (h1 : term6 n) : term65 n.
Proof. exact (proj1 (@lem4621060 n h1)). Qed.
Lemma lem4621243 (n : nat) : (term65 n) = ((term65 n) = True).
Proof. exact (@lem7 (term65 n)). Qed.
Lemma lem4621248 (k : nat) : (term63 k) = (term64 k).
Proof. exact (EQ_MP (@lem4621238 k) (@lem4621237 k)). Qed.
Lemma lem4621249 (n : nat) : (term63 n) = (term64 n).
Proof. exact (@lem4621248 n). Qed.
Lemma lem4621256 : (@FINITE nat) = (@FINITE nat).
Proof. exact (eq_refl (@FINITE nat)). Qed.
Lemma lem4621257 (n : nat) : (term66 n) = (term67 n).
Proof. exact (MK_COMB (@lem4621256) (@lem4621249 n)). Qed.
Lemma lem4621259 {A : Type'} (x : A) (s : A -> Prop) : (term53 A x s) = (@FINITE A s).
Proof. exact (EQ_MP (@lem4621217 A x s) (@lem4621216 A s x)). Qed.
Lemma lem4621260 (x : nat) (s : nat -> Prop) : (term68 x s) = (@FINITE nat s).
Proof. exact (@lem4621259 nat x s). Qed.
Lemma lem4621261 (n : nat) : (term67 n) = (term65 n).
Proof. exact (@lem4621260 n (term7 n)). Qed.
Lemma lem4621263 (n : nat) (h1 : term6 n) : (term65 n) = True.
Proof. exact (EQ_MP (@lem4621243 n) (@lem4621242 n h1)). Qed.
Lemma lem4621264 (n : nat) (h1 : term6 n) : (term67 n) = True.
Proof. exact (TRANS (@lem4621261 n) (@lem4621263 n h1)). Qed.
Lemma lem4621265 (n : nat) (h1 : term6 n) : (term66 n) = True.
Proof. exact (TRANS (@lem4621257 n) (@lem4621264 n h1)). Qed.
Lemma lem4621266 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4621267 (n : nat) (h1 : term6 n) : (term69 n) = (and True).
Proof. exact (MK_COMB (@lem4621266) (@lem4621265 n h1)). Qed.
Lemma lem4621271 (k : nat) : (term63 k) = (term64 k).
Proof. exact (EQ_MP (@lem4621238 k) (@lem4621237 k)). Qed.
Lemma lem4621272 (n : nat) : (term63 n) = (term64 n).
Proof. exact (@lem4621271 n). Qed.
Lemma lem4621279 : (@CARD nat) = (@CARD nat).
Proof. exact (eq_refl (@CARD nat)). Qed.
Lemma lem4621280 (n : nat) : (term70 n) = (term71 n).
Proof. exact (MK_COMB (@lem4621279) (@lem4621272 n)). Qed.
Lemma lem4621282 {A : Type'} (x : A) (s : A -> Prop) : term58 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4621227 A x s h0). Qed.
Lemma lem4621283 (x : nat) (s : nat -> Prop) : term72 x s.
Proof. exact (@lem4621282 nat x s). Qed.
Lemma lem4621284 (n : nat) : term73 n.
Proof. exact (@lem4621283 n (term7 n)). Qed.
Lemma lem4621286 (n : nat) (h1 : term6 n) : (term65 n) = True.
Proof. exact (EQ_MP (@lem4621243 n) (@lem4621242 n h1)). Qed.
Lemma lem4621287 (n : nat) (h1 : term6 n) : True = (term65 n).
Proof. exact (SYM (@lem4621286 n h1)). Qed.
Lemma lem4621288 (n : nat) (h1 : term6 n) : term65 n.
Proof. exact (EQ_MP (@lem4621287 n h1) (@lem0)). Qed.
Lemma lem4621289 (n : nat) (h1 : term6 n) : (term71 n) = (term74 n).
Proof. exact (@lem4621284 n (@lem4621288 n h1)). Qed.
Lemma lem4621291 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term75 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4621292 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term76 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4621291 _2963 g t e g' t' e'). Qed.
Lemma lem4621293 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term77 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4621292 _2963 g t e g' t'). Qed.
Lemma lem4621294 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term78 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4621293 _2963 g t e g'). Qed.
Lemma lem4621295 (g : Prop) (t : nat) (e : nat) : term79 g t e.
Proof. exact (@lem4621294 nat g t e). Qed.
Lemma lem4621296 (n : nat) : term80 n.
Proof. exact (@lem4621295 (term81 n) (term82 n) (term83 n)). Qed.
Lemma lem4621297 (n : nat) (g' : Prop) : term84 n g'.
Proof. exact (@lem4621296 n g'). Qed.
Lemma lem4621298 (n : nat) (g' : Prop) : (term84 n g') = (term85 n g').
Proof. exact (eq_refl (term84 n g')). Qed.
Lemma lem4621299 (n : nat) (g' : Prop) : term85 n g'.
Proof. exact (EQ_MP (@lem4621298 n g') (@lem4621297 n g')). Qed.
Lemma lem4621300 (n : nat) (g' : Prop) (t' : nat) : term86 n g' t'.
Proof. exact (@lem4621299 n g' t'). Qed.
Lemma lem4621301 (n : nat) (g' : Prop) (t' : nat) : (term86 n g' t') = (term87 n g' t').
Proof. exact (eq_refl (term86 n g' t')). Qed.
Lemma lem4621302 (n : nat) (g' : Prop) (t' : nat) : term87 n g' t'.
Proof. exact (EQ_MP (@lem4621301 n g' t') (@lem4621300 n g' t')). Qed.
Lemma lem4621303 (n : nat) (g' : Prop) (t' : nat) (e' : nat) : term88 n g' t' e'.
Proof. exact (@lem4621302 n g' t' e'). Qed.
Lemma lem4621304 (n : nat) (g' : Prop) (t' : nat) (e' : nat) : (term88 n g' t' e') = (term89 n g' t' e').
Proof. exact (eq_refl (term88 n g' t' e')). Qed.
Lemma lem4621305 (n : nat) (g' : Prop) (t' : nat) (e' : nat) : term89 n g' t' e'.
Proof. exact (EQ_MP (@lem4621304 n g' t' e') (@lem4621303 n g' t' e')). Qed.
Lemma lem4621307 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term49 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4621204 _83095 p x) (@lem4621203 _83095 p x)). Qed.
Lemma lem4621308 (p : nat -> Prop) (x : nat) : (term90 x p) = (p x).
Proof. exact (@lem4621307 nat p x). Qed.
Lemma lem4621309 (n : nat) : (term91 n) = (term92 n).
Proof. exact (@lem4621308 (term93 n) n). Qed.
Lemma lem4621310 (m : nat) (n : nat) : (term94 n m) = (Peano.lt m n).
Proof. exact (eq_refl (term94 n m)). Qed.
Lemma lem4621311 (GEN_PVAR_181 : nat) : (@SETSPEC nat GEN_PVAR_181) = (@SETSPEC nat GEN_PVAR_181).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_181)). Qed.
Lemma lem4621312 (GEN_PVAR_181 : nat) (m : nat) (n : nat) : (term95 GEN_PVAR_181 n m) = (term96 GEN_PVAR_181 m n).
Proof. exact (MK_COMB (@lem4621311 GEN_PVAR_181) (@lem4621310 m n)). Qed.
Lemma lem4621313 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem4621314 (GEN_PVAR_181 : nat) (n : nat) (m : nat) : (term97 GEN_PVAR_181 n m) = (term98 GEN_PVAR_181 n m).
Proof. exact (MK_COMB (@lem4621312 GEN_PVAR_181 m n) (@lem4621313 m)). Qed.
Lemma lem4621315 (GEN_PVAR_181 : nat) (n : nat) : (term99 GEN_PVAR_181 n) = (term100 GEN_PVAR_181 n).
Proof. exact (fun_ext (fun m : nat => @lem4621314 GEN_PVAR_181 n m)). Qed.
Lemma lem4621316 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem4621317 (GEN_PVAR_181 : nat) (n : nat) : (term101 GEN_PVAR_181 n) = (term102 GEN_PVAR_181 n).
Proof. exact (MK_COMB (@lem4621316) (@lem4621315 GEN_PVAR_181 n)). Qed.
Lemma lem4621318 (n : nat) : (term103 n) = (term104 n).
Proof. exact (fun_ext (fun GEN_PVAR_181 : nat => @lem4621317 GEN_PVAR_181 n)). Qed.
Lemma lem4621319 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem4621320 (n : nat) : (term105 n) = (term7 n).
Proof. exact (MK_COMB (@lem4621319) (@lem4621318 n)). Qed.
Lemma lem4621321 (n : nat) : (@IN nat n) = (@IN nat n).
Proof. exact (eq_refl (@IN nat n)). Qed.
Lemma lem4621322 (n : nat) : (term91 n) = (term81 n).
Proof. exact (MK_COMB (@lem4621321 n) (@lem4621320 n)). Qed.
Lemma lem4621323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4621324 (n : nat) : (term106 n) = (term107 n).
Proof. exact (MK_COMB (@lem4621323) (@lem4621322 n)). Qed.
Lemma lem4621325 (n : nat) : (term92 n) = (Peano.lt n n).
Proof. exact (eq_refl (term92 n)). Qed.
Lemma lem4621326 (n : nat) : ((term91 n) = (term92 n)) = ((term81 n) = (Peano.lt n n)).
Proof. exact (MK_COMB (@lem4621324 n) (@lem4621325 n)). Qed.
Lemma lem4621327 (n : nat) : (term81 n) = (Peano.lt n n).
Proof. exact (EQ_MP (@lem4621326 n) (@lem4621309 n)). Qed.
Lemma lem4621329 (n : nat) : (Peano.lt n n) = False.
Proof. exact (@lem4621173 n (@lem4621172 n)). Qed.
Lemma lem4621330 (n : nat) : (term81 n) = False.
Proof. exact (TRANS (@lem4621327 n) (@lem4621329 n)). Qed.
Lemma lem4621331 (n : nat) (t' : nat) (e' : nat) : term108 n t' e'.
Proof. exact (@lem4621305 n False t' e'). Qed.
Lemma lem4621332 (n : nat) (t' : nat) (e' : nat) : term109 n t' e'.
Proof. exact (@lem4621331 n t' e' (@lem4621330 n)). Qed.
Lemma lem4621337 (n : nat) (h1 : term6 n) : (term82 n) = n.
Proof. exact (proj2 (@lem4621060 n h1)). Qed.
Lemma lem4621338 (n : nat) (h1 : term6 n) : term110 n.
Proof. exact (fun h0 : False => @lem4621337 n h1). Qed.
Lemma lem4621339 (n : nat) (e' : nat) : term111 n e'.
Proof. exact (@lem4621332 n n e'). Qed.
Lemma lem4621340 (e' : nat) (n : nat) (h1 : term6 n) : term112 n e'.
Proof. exact (@lem4621339 n e' (@lem4621338 n h1)). Qed.
Lemma lem4621347 (n : nat) (h1 : term6 n) : (term82 n) = n.
Proof. exact (proj2 (@lem4621060 n h1)). Qed.
Lemma lem4621348 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem4621349 (n : nat) (h1 : term6 n) : (term83 n) = (S n).
Proof. exact (MK_COMB (@lem4621348) (@lem4621347 n h1)). Qed.
Lemma lem4621350 (n : nat) (h1 : term6 n) : term113 n.
Proof. exact (fun h0 : ~ False => @lem4621349 n h1). Qed.
Lemma lem4621351 (n : nat) (h1 : term6 n) : term114 n.
Proof. exact (@lem4621340 (S n) n h1). Qed.
Lemma lem4621352 (n : nat) (h1 : term6 n) : (term74 n) = (term115 n).
Proof. exact (@lem4621351 n h1 (@lem4621350 n h1)). Qed.
Lemma lem4621354 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4621355 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem4621354 nat t1 t2). Qed.
Lemma lem4621356 (n : nat) : (term115 n) = (S n).
Proof. exact (@lem4621355 n (S n)). Qed.
Lemma lem4621357 (n : nat) (h1 : term6 n) : (term74 n) = (S n).
Proof. exact (TRANS (@lem4621352 n h1) (@lem4621356 n)). Qed.
Lemma lem4621358 (n : nat) (h1 : term6 n) : (term71 n) = (S n).
Proof. exact (TRANS (@lem4621289 n h1) (@lem4621357 n h1)). Qed.
Lemma lem4621359 (n : nat) (h1 : term6 n) : (term70 n) = (S n).
Proof. exact (TRANS (@lem4621280 n) (@lem4621358 n h1)). Qed.
Lemma lem4621360 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4621361 (n : nat) (h1 : term6 n) : (term116 n) = (term117 n).
Proof. exact (MK_COMB (@lem4621360) (@lem4621359 n h1)). Qed.
Lemma lem4621362 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem4621363 (n : nat) (h1 : term6 n) : ((term70 n) = (S n)) = ((S n) = (S n)).
Proof. exact (MK_COMB (@lem4621361 n h1) (@lem4621362 n)). Qed.
Lemma lem4621365 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4621366 (x : nat) : (x = x) = True.
Proof. exact (@lem4621365 nat x). Qed.
Lemma lem4621367 (n : nat) : ((S n) = (S n)) = True.
Proof. exact (@lem4621366 (S n)). Qed.
Lemma lem4621368 (n : nat) (h1 : term6 n) : ((term70 n) = (S n)) = True.
Proof. exact (TRANS (@lem4621363 n h1) (@lem4621367 n)). Qed.
Lemma lem4621369 (n : nat) (h1 : term6 n) : (term22 n) = (True /\ True).
Proof. exact (MK_COMB (@lem4621267 n h1) (@lem4621368 n h1)). Qed.
Lemma lem4621371 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4621372 : (True /\ True) = True.
Proof. exact (@lem4621371 True). Qed.
Lemma lem4621373 (n : nat) (h1 : term6 n) : (term22 n) = True.
Proof. exact (TRANS (@lem4621369 n h1) (@lem4621372)). Qed.
Lemma lem4621374 (n : nat) (h1 : term6 n) : True = (term22 n).
Proof. exact (SYM (@lem4621373 n h1)). Qed.
Lemma lem4621375 (n : nat) (h1 : term6 n) : term22 n.
Proof. exact (EQ_MP (@lem4621374 n h1) (@lem0)). Qed.
Lemma lem4621376 (n : nat) : term24 n.
Proof. exact (fun h0 : term6 n => @lem4621375 n h0). Qed.
Lemma lem4621381 : term28.
Proof. exact (fun n : nat => @lem4621376 n). Qed.
Lemma lem4621382 : term30.
Proof. exact (conj (@lem4621169) (@lem4621381)). Qed.
Lemma lem4621383 : term11.
Proof. exact (@lem4621059 (@lem4621382)). Qed.
Lemma lem4621384 : term10.
Proof. exact (EQ_MP (@lem4621036) (@lem4621383)). Qed.
