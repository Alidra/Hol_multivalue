Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_EXISTS_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import ADD_EQ_0_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EXISTS_REFL_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import RIGHT_EXISTS_AND_THM_spec.
Require Import SUC_INJ_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm89498_spec.
Lemma lem99085 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem99086 {A : Type'} (x : A) (a : A) (h1 : x = a) : a = x.
Proof. exact (SYM (@lem99085 A x a h1)). Qed.
Lemma lem99087 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem99088 {A : Type'} (a : A) (x : A) (h1 : a = x) : x = a.
Proof. exact (SYM (@lem99087 A a x h1)). Qed.
Lemma lem99089 {A : Type'} (a : A) (x : A) : (x = a) = (a = x).
Proof. exact (prop_ext (fun h1 : x = a => @lem99086 A x a h1) (fun h1 : a = x => @lem99088 A a x h1)). Qed.
Lemma lem99090 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (fun_ext (fun x : A => @lem99089 A a x)). Qed.
Lemma lem99091 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem99092 {A : Type'} (a : A) : (term2 A a) = (term3 A a).
Proof. exact (MK_COMB (@lem99091 A) (@lem99090 A a)). Qed.
Lemma lem99093 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (fun_ext (fun a : A => @lem99092 A a)). Qed.
Lemma lem99094 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem99095 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem99094 A) (@lem99093 A)). Qed.
Lemma lem99096 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem99095 A) (@lem4363 A)). Qed.
Lemma lem99097 {A : Type'} (a : A) : term8 A a.
Proof. exact (@lem99096 A a). Qed.
Lemma lem99098 {A : Type'} (a : A) : (term8 A a) = (term3 A a).
Proof. exact (eq_refl (term8 A a)). Qed.
Lemma lem99099 {A : Type'} (a : A) : term3 A a.
Proof. exact (EQ_MP (@lem99098 A a) (@lem99097 A a)). Qed.
Lemma lem99100 {A : Type'} (a : A) : (term3 A a) = ((term3 A a) = True).
Proof. exact (@lem7 (term3 A a)). Qed.
Lemma lem99102 (m : nat) : term9 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem99103 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem99104 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem99103 m) (@lem99102 m)). Qed.
Lemma lem99105 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem99104 m n). Qed.
Lemma lem99106 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem99107 (m : nat) (n : nat) : term12 m n.
Proof. exact (EQ_MP (@lem99106 m n) (@lem99105 m n)). Qed.
Lemma lem99108 (m : nat) (n : nat) (p : nat) : term13 m n p.
Proof. exact (@lem99107 m n p). Qed.
Lemma lem99109 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term13 m n p)). Qed.
Lemma lem99111 (m : nat) : term14 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem99112 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem99113 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem99112 m) (@lem99111 m)). Qed.
Lemma lem99114 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem99113 m n). Qed.
Lemma lem99115 (m : nat) (n : nat) : (term16 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem99117 : term17.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem99118 : term18.
Proof. exact (proj2 (@lem99117)). Qed.
Lemma lem99119 : term19.
Proof. exact (proj2 (@lem99118)). Qed.
Lemma lem99120 (m : nat) : term20 m.
Proof. exact (@lem99119 m). Qed.
Lemma lem99121 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem99122 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem99121 m) (@lem99120 m)). Qed.
Lemma lem99123 (m : nat) (n : nat) : term22 m n.
Proof. exact (@lem99122 m n). Qed.
Lemma lem99124 (m : nat) (n : nat) : (term22 m n) = ((term23 m n) = (term24 m n)).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem99133 : term25.
Proof. exact (proj1 (@lem99117)). Qed.
Lemma lem99134 (m : nat) : term26 m.
Proof. exact (@lem99133 m). Qed.
Lemma lem99135 (m : nat) : (term26 m) = ((term27 m) = m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem99141 {A : Type'} (P : A -> Prop) : term28 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem99142 {A : Type'} (P : A -> Prop) : (term28 A P) = (term29 A P).
Proof. exact (eq_refl (term28 A P)). Qed.
Lemma lem99143 {A : Type'} (P : A -> Prop) : term29 A P.
Proof. exact (EQ_MP (@lem99142 A P) (@lem99141 A P)). Qed.
Lemma lem99144 {A : Type'} (P : A -> Prop) (Q : Prop) : term30 A P Q.
Proof. exact (@lem99143 A P Q). Qed.
Lemma lem99145 {A : Type'} (P : A -> Prop) (Q : Prop) : (term30 A P Q) = ((term31 A P Q) = (term32 A P Q)).
Proof. exact (eq_refl (term30 A P Q)). Qed.
Lemma lem99147 : term17.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem99148 : term18.
Proof. exact (proj2 (@lem99147)). Qed.
Lemma lem99149 : term19.
Proof. exact (proj2 (@lem99148)). Qed.
Lemma lem99150 (m : nat) : term20 m.
Proof. exact (@lem99149 m). Qed.
Lemma lem99151 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem99152 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem99151 m) (@lem99150 m)). Qed.
Lemma lem99153 (m : nat) (n : nat) : term22 m n.
Proof. exact (@lem99152 m n). Qed.
Lemma lem99154 (m : nat) (n : nat) : (term22 m n) = ((term23 m n) = (term24 m n)).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem99171 : term17.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem99172 : term18.
Proof. exact (proj2 (@lem99171)). Qed.
Lemma lem99180 : term33.
Proof. exact (proj1 (@lem99172)). Qed.
Lemma lem99181 (m : nat) : term34 m.
Proof. exact (@lem99180 m). Qed.
Lemma lem99182 (m : nat) : (term34 m) = (term35 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem99183 (m : nat) : term35 m.
Proof. exact (EQ_MP (@lem99182 m) (@lem99181 m)). Qed.
Lemma lem99184 (m : nat) (n : nat) : term36 m n.
Proof. exact (@lem99183 m n). Qed.
Lemma lem99185 (m : nat) (n : nat) : (term36 m n) = ((term37 m n) = (term24 m n)).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem99187 : term25.
Proof. exact (proj1 (@lem99171)). Qed.
Lemma lem99188 (m : nat) : term26 m.
Proof. exact (@lem99187 m). Qed.
Lemma lem99189 (m : nat) : (term26 m) = ((term27 m) = m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem99195 {A : Type'} (a : A) : term38 A a.
Proof. exact (@lem4363 A a). Qed.
Lemma lem99196 {A : Type'} (a : A) : (term38 A a) = (term2 A a).
Proof. exact (eq_refl (term38 A a)). Qed.
Lemma lem99197 {A : Type'} (a : A) : term2 A a.
Proof. exact (EQ_MP (@lem99196 A a) (@lem99195 A a)). Qed.
Lemma lem99198 {A : Type'} (a : A) : (term2 A a) = ((term2 A a) = True).
Proof. exact (@lem7 (term2 A a)). Qed.
Lemma lem99200 {A : Type'} (P : Prop) : term39 A P.
Proof. exact (@lem5751 A P). Qed.
Lemma lem99201 {A : Type'} (P : Prop) : (term39 A P) = (term40 A P).
Proof. exact (eq_refl (term39 A P)). Qed.
Lemma lem99202 {A : Type'} (P : Prop) : term40 A P.
Proof. exact (EQ_MP (@lem99201 A P) (@lem99200 A P)). Qed.
Lemma lem99203 {A : Type'} (P : Prop) (Q : A -> Prop) : term41 A P Q.
Proof. exact (@lem99202 A P Q). Qed.
Lemma lem99204 {A : Type'} (P : Prop) (Q : A -> Prop) : (term41 A P Q) = ((term42 A P Q) = (term43 A P Q)).
Proof. exact (eq_refl (term41 A P Q)). Qed.
Lemma lem99206 (m : nat) : term44 m.
Proof. exact (@lem79432 m). Qed.
Lemma lem99207 (m : nat) : (term44 m) = (term45 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem99208 (m : nat) : term45 m.
Proof. exact (EQ_MP (@lem99207 m) (@lem99206 m)). Qed.
Lemma lem99209 (m : nat) (n : nat) : term46 m n.
Proof. exact (@lem99208 m n). Qed.
Lemma lem99210 (m : nat) (n : nat) : (term46 m n) = (((Nat.add m n) = (NUMERAL 0)) = (term47 m n)).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem99211 (m : nat) (n : nat) : ((Nat.add m n) = (NUMERAL 0)) = (term47 m n).
Proof. exact (EQ_MP (@lem99210 m n) (@lem99209 m n)). Qed.
Lemma lem99212 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (Nat.add m n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem99213 (m : nat) (n : nat) (h1 : (Nat.add m n) = (NUMERAL 0)) : (NUMERAL 0) = (Nat.add m n).
Proof. exact (SYM (@lem99212 m n h1)). Qed.
Lemma lem99214 (m : nat) (n : nat) (h1 : (NUMERAL 0) = (Nat.add m n)) : (NUMERAL 0) = (Nat.add m n).
Proof. exact (h1). Qed.
Lemma lem99215 (m : nat) (n : nat) (h1 : (NUMERAL 0) = (Nat.add m n)) : (Nat.add m n) = (NUMERAL 0).
Proof. exact (SYM (@lem99214 m n h1)). Qed.
Lemma lem99216 (m : nat) (n : nat) : ((Nat.add m n) = (NUMERAL 0)) = ((NUMERAL 0) = (Nat.add m n)).
Proof. exact (prop_ext (fun h1 : (Nat.add m n) = (NUMERAL 0) => @lem99213 m n h1) (fun h1 : (NUMERAL 0) = (Nat.add m n) => @lem99215 m n h1)). Qed.
Lemma lem99217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem99218 (m : nat) (n : nat) : (term48 m n) = (term49 m n).
Proof. exact (MK_COMB (@lem99217) (@lem99216 m n)). Qed.
Lemma lem99219 (m : nat) (n : nat) : (term47 m n) = (term47 m n).
Proof. exact (eq_refl (term47 m n)). Qed.
Lemma lem99220 (m : nat) (n : nat) : (((Nat.add m n) = (NUMERAL 0)) = (term47 m n)) = (((NUMERAL 0) = (Nat.add m n)) = (term47 m n)).
Proof. exact (MK_COMB (@lem99218 m n) (@lem99219 m n)). Qed.
Lemma lem99223 (P : nat -> Prop) : term50 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem99224 (m : nat) : term51 m.
Proof. exact (@lem99223 (term52 m)). Qed.
Lemma lem99225 (m : nat) : (term53 m) = ((term54 m) = (term55 m)).
Proof. exact (eq_refl (term53 m)). Qed.
Lemma lem99226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem99227 (m : nat) : (term56 m) = (term57 m).
Proof. exact (MK_COMB (@lem99226) (@lem99225 m)). Qed.
Lemma lem99228 (n : nat) (m : nat) : (term58 m n) = ((Peano.le m n) = (term59 n m)).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem99229 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem99230 (n : nat) (m : nat) : (term60 m n) = (term61 n m).
Proof. exact (MK_COMB (@lem99229) (@lem99228 n m)). Qed.
Lemma lem99231 (n : nat) (m : nat) : (term62 m n) = ((term63 m n) = (term64 n m)).
Proof. exact (eq_refl (term62 m n)). Qed.
Lemma lem99232 (n : nat) (m : nat) : (term65 m n) = (term66 n m).
Proof. exact (MK_COMB (@lem99230 n m) (@lem99231 n m)). Qed.
Lemma lem99233 (m : nat) : (term67 m) = (term68 m).
Proof. exact (fun_ext (fun n : nat => @lem99232 n m)). Qed.
Lemma lem99234 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem99235 (m : nat) : (term69 m) = (term70 m).
Proof. exact (MK_COMB (@lem99234) (@lem99233 m)). Qed.
Lemma lem99236 (m : nat) : (term71 m) = (term72 m).
Proof. exact (MK_COMB (@lem99227 m) (@lem99235 m)). Qed.
Lemma lem99237 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem99238 (m : nat) : (term73 m) = (term74 m).
Proof. exact (MK_COMB (@lem99237) (@lem99236 m)). Qed.
Lemma lem99239 (n : nat) (m : nat) : (term58 m n) = ((Peano.le m n) = (term59 n m)).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem99240 (m : nat) : (term75 m) = (term52 m).
Proof. exact (fun_ext (fun n : nat => @lem99239 n m)). Qed.
Lemma lem99241 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem99242 (m : nat) : (term76 m) = (term77 m).
Proof. exact (MK_COMB (@lem99241) (@lem99240 m)). Qed.
Lemma lem99243 (m : nat) : (term51 m) = (term78 m).
Proof. exact (MK_COMB (@lem99238 m) (@lem99242 m)). Qed.
Lemma lem99244 (m : nat) : term78 m.
Proof. exact (EQ_MP (@lem99243 m) (@lem99224 m)). Qed.
Lemma lem99253 : term79.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem99254 (m : nat) : term80 m.
Proof. exact (@lem99253 m). Qed.
Lemma lem99255 (m : nat) : (term80 m) = ((term54 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term80 m)). Qed.
Lemma lem99260 (m : nat) : (term54 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem99255 m) (@lem99254 m)). Qed.
Lemma lem99263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem99264 (m : nat) : (term81 m) = (term82 m).
Proof. exact (MK_COMB (@lem99263) (@lem99260 m)). Qed.
Lemma lem99271 (m : nat) : (term55 m) = (term55 m).
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem99272 (m : nat) : ((term54 m) = (term55 m)) = ((m = (NUMERAL 0)) = (term55 m)).
Proof. exact (MK_COMB (@lem99264 m) (@lem99271 m)). Qed.
Lemma lem99275 (m : nat) : ((m = (NUMERAL 0)) = (term55 m)) = ((term54 m) = (term55 m)).
Proof. exact (SYM (@lem99272 m)). Qed.
Lemma lem99276 : term83.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem99277 (m : nat) : term84 m.
Proof. exact (@lem99276 m). Qed.
Lemma lem99278 (m : nat) : (term84 m) = (term85 m).
Proof. exact (eq_refl (term84 m)). Qed.
Lemma lem99279 (m : nat) : term85 m.
Proof. exact (EQ_MP (@lem99278 m) (@lem99277 m)). Qed.
Lemma lem99280 (m : nat) (n : nat) : term86 m n.
Proof. exact (@lem99279 m n). Qed.
Lemma lem99281 (m : nat) (n : nat) : (term86 m n) = ((term63 m n) = (term87 m n)).
Proof. exact (eq_refl (term86 m n)). Qed.
Lemma lem99290 (m : nat) (n : nat) : (term63 m n) = (term87 m n).
Proof. exact (EQ_MP (@lem99281 m n) (@lem99280 m n)). Qed.
Lemma lem99296 (n : nat) (m : nat) (h1 : (Peano.le m n) = (term59 n m)) : (Peano.le m n) = (term59 n m).
Proof. exact (h1). Qed.
Lemma lem99303 (m : nat) (n : nat) : (term88 m n) = (term88 m n).
Proof. exact (eq_refl (term88 m n)). Qed.
Lemma lem99304 (n : nat) (m : nat) (h1 : (Peano.le m n) = (term59 n m)) : (term87 m n) = (term89 n m).
Proof. exact (MK_COMB (@lem99303 m n) (@lem99296 n m h1)). Qed.
Lemma lem99307 (n : nat) (m : nat) (h1 : (Peano.le m n) = (term59 n m)) : (term63 m n) = (term89 n m).
Proof. exact (TRANS (@lem99290 m n) (@lem99304 n m h1)). Qed.
Lemma lem99308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem99309 (n : nat) (m : nat) (h1 : (Peano.le m n) = (term59 n m)) : (term90 m n) = (term91 n m).
Proof. exact (MK_COMB (@lem99308) (@lem99307 n m h1)). Qed.
Lemma lem99316 (n : nat) (m : nat) : (term64 n m) = (term64 n m).
Proof. exact (eq_refl (term64 n m)). Qed.
Lemma lem99317 (n : nat) (m : nat) (h1 : (Peano.le m n) = (term59 n m)) : ((term63 m n) = (term64 n m)) = ((term89 n m) = (term64 n m)).
Proof. exact (MK_COMB (@lem99309 n m h1) (@lem99316 n m)). Qed.
Lemma lem99320 (n : nat) (m : nat) (h1 : (Peano.le m n) = (term59 n m)) : ((term89 n m) = (term64 n m)) = ((term63 m n) = (term64 n m)).
Proof. exact (SYM (@lem99317 n m h1)). Qed.
Lemma lem99330 (m : nat) (n : nat) : ((NUMERAL 0) = (Nat.add m n)) = (term47 m n).
Proof. exact (EQ_MP (@lem99220 m n) (@lem99211 m n)). Qed.
Lemma lem99331 (m : nat) (d : nat) : ((NUMERAL 0) = (Nat.add m d)) = (term47 m d).
Proof. exact (@lem99330 m d). Qed.
Lemma lem99338 (m : nat) : (term92 m) = (term93 m).
Proof. exact (fun_ext (fun d : nat => @lem99331 m d)). Qed.
Lemma lem99339 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem99340 (m : nat) : (term55 m) = (term94 m).
Proof. exact (MK_COMB (@lem99339) (@lem99338 m)). Qed.
Lemma lem99345 (m : nat) : (term82 m) = (term82 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem99346 (m : nat) : ((m = (NUMERAL 0)) = (term55 m)) = ((m = (NUMERAL 0)) = (term94 m)).
Proof. exact (MK_COMB (@lem99345 m) (@lem99340 m)). Qed.
Lemma lem99349 (m : nat) : ((m = (NUMERAL 0)) = (term94 m)) = ((m = (NUMERAL 0)) = (term55 m)).
Proof. exact (SYM (@lem99346 m)). Qed.
Lemma lem99355 {A : Type'} (P : Prop) (Q : A -> Prop) : (term42 A P Q) = (term43 A P Q).
Proof. exact (EQ_MP (@lem99204 A P Q) (@lem99203 A P Q)). Qed.
Lemma lem99356 (P : Prop) (Q : nat -> Prop) : (term95 P Q) = (term96 P Q).
Proof. exact (@lem99355 nat P Q). Qed.
Lemma lem99357 (m : nat) : (term97 m) = (term98 m).
Proof. exact (@lem99356 (m = (NUMERAL 0)) term99). Qed.
Lemma lem99358 (d : nat) : (term100 d) = (d = (NUMERAL 0)).
Proof. exact (eq_refl (term100 d)). Qed.
Lemma lem99359 (m : nat) : (term101 m) = (term101 m).
Proof. exact (eq_refl (term101 m)). Qed.
Lemma lem99360 (m : nat) (d : nat) : (term102 m d) = (term47 m d).
Proof. exact (MK_COMB (@lem99359 m) (@lem99358 d)). Qed.
Lemma lem99361 (m : nat) : (term103 m) = (term93 m).
Proof. exact (fun_ext (fun d : nat => @lem99360 m d)). Qed.
Lemma lem99362 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem99363 (m : nat) : (term97 m) = (term94 m).
Proof. exact (MK_COMB (@lem99362) (@lem99361 m)). Qed.
Lemma lem99364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem99365 (m : nat) : (term104 m) = (term105 m).
Proof. exact (MK_COMB (@lem99364) (@lem99363 m)). Qed.
Lemma lem99366 (d : nat) : (term100 d) = (d = (NUMERAL 0)).
Proof. exact (eq_refl (term100 d)). Qed.
Lemma lem99367 : term106 = term99.
Proof. exact (fun_ext (fun d : nat => @lem99366 d)). Qed.
Lemma lem99368 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem99369 : term107 = term108.
Proof. exact (MK_COMB (@lem99368) (@lem99367)). Qed.
Lemma lem99370 (m : nat) : (term101 m) = (term101 m).
Proof. exact (eq_refl (term101 m)). Qed.
Lemma lem99371 (m : nat) : (term98 m) = (term109 m).
Proof. exact (MK_COMB (@lem99370 m) (@lem99369)). Qed.
Lemma lem99372 (m : nat) : ((term97 m) = (term98 m)) = ((term94 m) = (term109 m)).
Proof. exact (MK_COMB (@lem99365 m) (@lem99371 m)). Qed.
Lemma lem99373 (m : nat) : (term94 m) = (term109 m).
Proof. exact (EQ_MP (@lem99372 m) (@lem99357 m)). Qed.
Lemma lem99379 {A : Type'} (a : A) : (term2 A a) = True.
Proof. exact (EQ_MP (@lem99198 A a) (@lem99197 A a)). Qed.
Lemma lem99380 (a : nat) : (term110 a) = True.
Proof. exact (@lem99379 nat a). Qed.
Lemma lem99381 : term108 = True.
Proof. exact (@lem99380 (NUMERAL 0)). Qed.
Lemma lem99382 (m : nat) : (term101 m) = (term101 m).
Proof. exact (eq_refl (term101 m)). Qed.
Lemma lem99383 (m : nat) : (term109 m) = (term111 m).
Proof. exact (MK_COMB (@lem99382 m) (@lem99381)). Qed.
Lemma lem99385 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem99386 (m : nat) : (term111 m) = (m = (NUMERAL 0)).
Proof. exact (@lem99385 (m = (NUMERAL 0))). Qed.
Lemma lem99389 (m : nat) : (term109 m) = (m = (NUMERAL 0)).
Proof. exact (TRANS (@lem99383 m) (@lem99386 m)). Qed.
Lemma lem99390 (m : nat) : (term94 m) = (m = (NUMERAL 0)).
Proof. exact (TRANS (@lem99373 m) (@lem99389 m)). Qed.
Lemma lem99391 (m : nat) : (term82 m) = (term82 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem99392 (m : nat) : ((m = (NUMERAL 0)) = (term94 m)) = ((m = (NUMERAL 0)) = (m = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem99391 m) (@lem99390 m)). Qed.
Lemma lem99394 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem99395 (x : Prop) : (x = x) = True.
Proof. exact (@lem99394 Prop x). Qed.
Lemma lem99396 (m : nat) : ((m = (NUMERAL 0)) = (m = (NUMERAL 0))) = True.
Proof. exact (@lem99395 (m = (NUMERAL 0))). Qed.
Lemma lem99397 (m : nat) : ((m = (NUMERAL 0)) = (term94 m)) = True.
Proof. exact (TRANS (@lem99392 m) (@lem99396 m)). Qed.
Lemma lem99398 (m : nat) : True = ((m = (NUMERAL 0)) = (term94 m)).
Proof. exact (SYM (@lem99397 m)). Qed.
Lemma lem99399 (m : nat) : (m = (NUMERAL 0)) = (term94 m).
Proof. exact (EQ_MP (@lem99398 m) (@lem0)). Qed.
Lemma lem99400 (m : nat) : (m = (NUMERAL 0)) = (term55 m).
Proof. exact (EQ_MP (@lem99349 m) (@lem99399 m)). Qed.
Lemma lem99401 (n : nat) (m : nat) (h1 : term89 n m) : term89 n m.
Proof. exact (h1). Qed.
Lemma lem99402 (m : nat) (n : nat) (h1 : m = (S n)) : m = (S n).
Proof. exact (h1). Qed.
Lemma lem99403 (n : nat) (m : nat) (h1 : term59 n m) : term59 n m.
Proof. exact (h1). Qed.
Lemma lem99404 (n : nat) : (term112 n) = (term112 n).
Proof. exact (eq_refl (term112 n)). Qed.
Lemma lem99405 (m : nat) (n : nat) (h1 : m = (S n)) : (term113 n m) = (term114 n).
Proof. exact (MK_COMB (@lem99404 n) (@lem99402 m n h1)). Qed.
Lemma lem99406 (n : nat) : (term114 n) = (term115 n).
Proof. exact (eq_refl (term114 n)). Qed.
Lemma lem99407 (n : nat) (m : nat) : (term116 n m) = (term116 n m).
Proof. exact (eq_refl (term116 n m)). Qed.
Lemma lem99408 (m : nat) (n : nat) : ((term113 n m) = (term114 n)) = ((term113 n m) = (term115 n)).
Proof. exact (MK_COMB (@lem99407 n m) (@lem99406 n)). Qed.
Lemma lem99409 (n : nat) (m : nat) : (term113 n m) = (term64 n m).
Proof. exact (eq_refl (term113 n m)). Qed.
Lemma lem99410 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem99411 (n : nat) (m : nat) : (term116 n m) = (term117 n m).
Proof. exact (MK_COMB (@lem99410) (@lem99409 n m)). Qed.
Lemma lem99412 (n : nat) : (term115 n) = (term115 n).
Proof. exact (eq_refl (term115 n)). Qed.
Lemma lem99413 (m : nat) (n : nat) : ((term113 n m) = (term115 n)) = ((term64 n m) = (term115 n)).
Proof. exact (MK_COMB (@lem99411 n m) (@lem99412 n)). Qed.
Lemma lem99414 (m : nat) (n : nat) : ((term113 n m) = (term114 n)) = ((term64 n m) = (term115 n)).
Proof. exact (TRANS (@lem99408 m n) (@lem99413 m n)). Qed.
Lemma lem99415 (m : nat) (n : nat) (h1 : m = (S n)) : (term64 n m) = (term115 n).
Proof. exact (EQ_MP (@lem99414 m n) (@lem99405 m n h1)). Qed.
Lemma lem99416 (m : nat) (n : nat) (h1 : m = (S n)) : (term115 n) = (term64 n m).
Proof. exact (SYM (@lem99415 m n h1)). Qed.
Lemma lem99420 (m : nat) (n : nat) : (term37 m n) = (term24 m n).
Proof. exact (EQ_MP (@lem99185 m n) (@lem99184 m n)). Qed.
Lemma lem99421 (n : nat) : (term118 n) = (term119 n).
Proof. exact (@lem99420 n (NUMERAL 0)). Qed.
Lemma lem99423 (m : nat) : (term27 m) = m.
Proof. exact (EQ_MP (@lem99189 m) (@lem99188 m)). Qed.
Lemma lem99424 (n : nat) : (term27 n) = n.
Proof. exact (@lem99423 n). Qed.
Lemma lem99425 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem99426 (n : nat) : (term119 n) = (S n).
Proof. exact (MK_COMB (@lem99425) (@lem99424 n)). Qed.
Lemma lem99427 (n : nat) : (term118 n) = (S n).
Proof. exact (TRANS (@lem99421 n) (@lem99426 n)). Qed.
Lemma lem99428 (n : nat) : (term120 n) = (term120 n).
Proof. exact (eq_refl (term120 n)). Qed.
Lemma lem99429 (n : nat) : ((S n) = (term118 n)) = ((S n) = (S n)).
Proof. exact (MK_COMB (@lem99428 n) (@lem99427 n)). Qed.
Lemma lem99431 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem99432 (x : nat) : (x = x) = True.
Proof. exact (@lem99431 nat x). Qed.
Lemma lem99433 (n : nat) : ((S n) = (S n)) = True.
Proof. exact (@lem99432 (S n)). Qed.
Lemma lem99434 (n : nat) : ((S n) = (term118 n)) = True.
Proof. exact (TRANS (@lem99429 n) (@lem99433 n)). Qed.
Lemma lem99435 (n : nat) : True = ((S n) = (term118 n)).
Proof. exact (SYM (@lem99434 n)). Qed.
Lemma lem99436 (n : nat) : (S n) = (term118 n).
Proof. exact (EQ_MP (@lem99435 n) (@lem0)). Qed.
Lemma lem99437 (n : nat) : term115 n.
Proof. exact (ex_intro (term121 n) (NUMERAL 0) (@lem99436 n)). Qed.
Lemma lem99438 (n : nat) (m : nat) (h1 : term59 n m) : term59 n m.
Proof. exact (h1). Qed.
Lemma lem99439 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem99440 (m : nat) : (term122 m) = (term122 m).
Proof. exact (eq_refl (term122 m)). Qed.
Lemma lem99441 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term123 m n) = (term124 m d).
Proof. exact (MK_COMB (@lem99440 m) (@lem99439 n m d h1)). Qed.
Lemma lem99442 (d : nat) (m : nat) : (term124 m d) = (term125 d m).
Proof. exact (eq_refl (term124 m d)). Qed.
Lemma lem99443 (m : nat) (n : nat) : (term126 m n) = (term126 m n).
Proof. exact (eq_refl (term126 m n)). Qed.
Lemma lem99444 (n : nat) (d : nat) (m : nat) : ((term123 m n) = (term124 m d)) = ((term123 m n) = (term125 d m)).
Proof. exact (MK_COMB (@lem99443 m n) (@lem99442 d m)). Qed.
Lemma lem99445 (n : nat) (m : nat) : (term123 m n) = (term64 n m).
Proof. exact (eq_refl (term123 m n)). Qed.
Lemma lem99446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem99447 (n : nat) (m : nat) : (term126 m n) = (term117 n m).
Proof. exact (MK_COMB (@lem99446) (@lem99445 n m)). Qed.
Lemma lem99448 (d : nat) (m : nat) : (term125 d m) = (term125 d m).
Proof. exact (eq_refl (term125 d m)). Qed.
Lemma lem99449 (n : nat) (d : nat) (m : nat) : ((term123 m n) = (term125 d m)) = ((term64 n m) = (term125 d m)).
Proof. exact (MK_COMB (@lem99447 n m) (@lem99448 d m)). Qed.
Lemma lem99450 (n : nat) (d : nat) (m : nat) : ((term123 m n) = (term124 m d)) = ((term64 n m) = (term125 d m)).
Proof. exact (TRANS (@lem99444 n d m) (@lem99449 n d m)). Qed.
Lemma lem99451 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term64 n m) = (term125 d m).
Proof. exact (EQ_MP (@lem99450 n d m) (@lem99441 n m d h1)). Qed.
Lemma lem99452 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term125 d m) = (term64 n m).
Proof. exact (SYM (@lem99451 n m d h1)). Qed.
Lemma lem99456 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (EQ_MP (@lem99154 m n) (@lem99153 m n)). Qed.
Lemma lem99457 (m : nat) (d : nat) : (term23 m d) = (term24 m d).
Proof. exact (@lem99456 m d). Qed.
Lemma lem99458 (m : nat) (d : nat) : (term127 m d) = (term127 m d).
Proof. exact (eq_refl (term127 m d)). Qed.
Lemma lem99459 (m : nat) (d : nat) : ((term24 m d) = (term23 m d)) = ((term24 m d) = (term24 m d)).
Proof. exact (MK_COMB (@lem99458 m d) (@lem99457 m d)). Qed.
Lemma lem99461 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem99462 (x : nat) : (x = x) = True.
Proof. exact (@lem99461 nat x). Qed.
Lemma lem99463 (m : nat) (d : nat) : ((term24 m d) = (term24 m d)) = True.
Proof. exact (@lem99462 (term24 m d)). Qed.
Lemma lem99464 (m : nat) (d : nat) : ((term24 m d) = (term23 m d)) = True.
Proof. exact (TRANS (@lem99459 m d) (@lem99463 m d)). Qed.
Lemma lem99465 (m : nat) (d : nat) : True = ((term24 m d) = (term23 m d)).
Proof. exact (SYM (@lem99464 m d)). Qed.
Lemma lem99466 (m : nat) (d : nat) : (term24 m d) = (term23 m d).
Proof. exact (EQ_MP (@lem99465 m d) (@lem0)). Qed.
Lemma lem99467 (d : nat) (m : nat) : term125 d m.
Proof. exact (ex_intro (term128 d m) (S d) (@lem99466 m d)). Qed.
Lemma lem99468 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : term64 n m.
Proof. exact (EQ_MP (@lem99452 n m d h1) (@lem99467 d m)). Qed.
Lemma lem99469 (n : nat) (m : nat) (h1 : term59 n m) : term64 n m.
Proof. exact (ex_elim (@lem99438 n m h1) (fun d : nat => fun h0 : term129 n m d => @lem99468 n m d h0)). Qed.
Lemma lem99470 (n : nat) (m : nat) : term130 n m.
Proof. exact (fun h0 : term59 n m => @lem99469 n m h0). Qed.
Lemma lem99471 (n : nat) (m : nat) (h1 : term59 n m) : term64 n m.
Proof. exact (@lem99470 n m (@lem99403 n m h1)). Qed.
Lemma lem99472 (m : nat) (n : nat) (h1 : m = (S n)) : term64 n m.
Proof. exact (EQ_MP (@lem99416 m n h1) (@lem99437 n)). Qed.
Lemma lem99473 (n : nat) (m : nat) (h1 : term89 n m) : term64 n m.
Proof. exact (or_elim (@lem99401 n m h1) (fun h0 : m = (S n) => @lem99472 m n h0) (fun h0 : term59 n m => @lem99471 n m h0)). Qed.
Lemma lem99474 (n : nat) (m : nat) : term131 n m.
Proof. exact (fun h0 : term89 n m => @lem99473 n m h0). Qed.
Lemma lem99476 {A : Type'} (P : A -> Prop) (Q : Prop) : (term31 A P Q) = (term32 A P Q).
Proof. exact (EQ_MP (@lem99145 A P Q) (@lem99144 A P Q)). Qed.
Lemma lem99477 (P : nat -> Prop) (Q : Prop) : (term132 P Q) = (term133 P Q).
Proof. exact (@lem99476 nat P Q). Qed.
Lemma lem99478 (n : nat) (m : nat) : (term134 n m) = (term135 n m).
Proof. exact (@lem99477 (term136 n m) (term89 n m)). Qed.
Lemma lem99479 (n : nat) (m : nat) (d : nat) : (term137 n m d) = ((S n) = (Nat.add m d)).
Proof. exact (eq_refl (term137 n m d)). Qed.
Lemma lem99480 (n : nat) (m : nat) : (term138 n m) = (term136 n m).
Proof. exact (fun_ext (fun d : nat => @lem99479 n m d)). Qed.
Lemma lem99481 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem99482 (n : nat) (m : nat) : (term139 n m) = (term64 n m).
Proof. exact (MK_COMB (@lem99481) (@lem99480 n m)). Qed.
Lemma lem99483 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem99484 (n : nat) (m : nat) : (term140 n m) = (term141 n m).
Proof. exact (MK_COMB (@lem99483) (@lem99482 n m)). Qed.
Lemma lem99485 (n : nat) (m : nat) : (term89 n m) = (term89 n m).
Proof. exact (eq_refl (term89 n m)). Qed.
Lemma lem99486 (n : nat) (m : nat) : (term134 n m) = (term142 n m).
Proof. exact (MK_COMB (@lem99484 n m) (@lem99485 n m)). Qed.
Lemma lem99487 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem99488 (n : nat) (m : nat) : (term143 n m) = (term144 n m).
Proof. exact (MK_COMB (@lem99487) (@lem99486 n m)). Qed.
Lemma lem99489 (n : nat) (m : nat) (d : nat) : (term137 n m d) = ((S n) = (Nat.add m d)).
Proof. exact (eq_refl (term137 n m d)). Qed.
Lemma lem99490 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem99491 (n : nat) (m : nat) (d : nat) : (term145 n m d) = (term146 n m d).
Proof. exact (MK_COMB (@lem99490) (@lem99489 n m d)). Qed.
Lemma lem99492 (n : nat) (m : nat) : (term89 n m) = (term89 n m).
Proof. exact (eq_refl (term89 n m)). Qed.
Lemma lem99493 (d : nat) (n : nat) (m : nat) : (term147 d n m) = (term148 d n m).
Proof. exact (MK_COMB (@lem99491 n m d) (@lem99492 n m)). Qed.
Lemma lem99494 (n : nat) (m : nat) : (term149 n m) = (term150 n m).
Proof. exact (fun_ext (fun d : nat => @lem99493 d n m)). Qed.
Lemma lem99495 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem99496 (n : nat) (m : nat) : (term135 n m) = (term151 n m).
Proof. exact (MK_COMB (@lem99495) (@lem99494 n m)). Qed.
Lemma lem99497 (n : nat) (m : nat) : ((term134 n m) = (term135 n m)) = ((term142 n m) = (term151 n m)).
Proof. exact (MK_COMB (@lem99488 n m) (@lem99496 n m)). Qed.
Lemma lem99498 (n : nat) (m : nat) : (term142 n m) = (term151 n m).
Proof. exact (EQ_MP (@lem99497 n m) (@lem99478 n m)). Qed.
Lemma lem99499 (n : nat) (m : nat) : (term151 n m) = (term142 n m).
Proof. exact (SYM (@lem99498 n m)). Qed.
Lemma lem99501 (P : nat -> Prop) : term50 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem99502 (n : nat) (m : nat) : term152 n m.
Proof. exact (@lem99501 (term150 n m)). Qed.
Lemma lem99503 (n : nat) (m : nat) : (term153 n m) = (term154 n m).
Proof. exact (eq_refl (term153 n m)). Qed.
Lemma lem99504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem99505 (n : nat) (m : nat) : (term155 n m) = (term156 n m).
Proof. exact (MK_COMB (@lem99504) (@lem99503 n m)). Qed.
Lemma lem99506 (d : nat) (n : nat) (m : nat) : (term157 n m d) = (term148 d n m).
Proof. exact (eq_refl (term157 n m d)). Qed.
Lemma lem99507 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem99508 (d : nat) (n : nat) (m : nat) : (term158 n m d) = (term159 d n m).
Proof. exact (MK_COMB (@lem99507) (@lem99506 d n m)). Qed.
Lemma lem99509 (d : nat) (n : nat) (m : nat) : (term160 n m d) = (term161 d n m).
Proof. exact (eq_refl (term160 n m d)). Qed.
Lemma lem99510 (d : nat) (n : nat) (m : nat) : (term162 n m d) = (term163 d n m).
Proof. exact (MK_COMB (@lem99508 d n m) (@lem99509 d n m)). Qed.
Lemma lem99511 (n : nat) (m : nat) : (term164 n m) = (term165 n m).
Proof. exact (fun_ext (fun d : nat => @lem99510 d n m)). Qed.
Lemma lem99512 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem99513 (n : nat) (m : nat) : (term166 n m) = (term167 n m).
Proof. exact (MK_COMB (@lem99512) (@lem99511 n m)). Qed.
Lemma lem99514 (n : nat) (m : nat) : (term168 n m) = (term169 n m).
Proof. exact (MK_COMB (@lem99505 n m) (@lem99513 n m)). Qed.
Lemma lem99515 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem99516 (n : nat) (m : nat) : (term170 n m) = (term171 n m).
Proof. exact (MK_COMB (@lem99515) (@lem99514 n m)). Qed.
Lemma lem99517 (d : nat) (n : nat) (m : nat) : (term157 n m d) = (term148 d n m).
Proof. exact (eq_refl (term157 n m d)). Qed.
Lemma lem99518 (n : nat) (m : nat) : (term172 n m) = (term150 n m).
Proof. exact (fun_ext (fun d : nat => @lem99517 d n m)). Qed.
Lemma lem99519 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem99520 (n : nat) (m : nat) : (term173 n m) = (term151 n m).
Proof. exact (MK_COMB (@lem99519) (@lem99518 n m)). Qed.
Lemma lem99521 (n : nat) (m : nat) : (term152 n m) = (term174 n m).
Proof. exact (MK_COMB (@lem99516 n m) (@lem99520 n m)). Qed.
Lemma lem99522 (n : nat) (m : nat) : term174 n m.
Proof. exact (EQ_MP (@lem99521 n m) (@lem99502 n m)). Qed.
Lemma lem99531 (m : nat) : (term27 m) = m.
Proof. exact (EQ_MP (@lem99135 m) (@lem99134 m)). Qed.
Lemma lem99532 (n : nat) : (term120 n) = (term120 n).
Proof. exact (eq_refl (term120 n)). Qed.
Lemma lem99533 (n : nat) (m : nat) : ((S n) = (term27 m)) = ((S n) = m).
Proof. exact (MK_COMB (@lem99532 n) (@lem99531 m)). Qed.
Lemma lem99536 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem99537 (n : nat) (m : nat) : (term175 n m) = (term176 n m).
Proof. exact (MK_COMB (@lem99536) (@lem99533 n m)). Qed.
Lemma lem99548 (n : nat) (m : nat) : (term89 n m) = (term89 n m).
Proof. exact (eq_refl (term89 n m)). Qed.
Lemma lem99549 (n : nat) (m : nat) : (term154 n m) = (term177 n m).
Proof. exact (MK_COMB (@lem99537 n m) (@lem99548 n m)). Qed.
Lemma lem99554 (n : nat) (m : nat) : (term177 n m) = (term154 n m).
Proof. exact (SYM (@lem99549 n m)). Qed.
Lemma lem99562 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (EQ_MP (@lem99124 m n) (@lem99123 m n)). Qed.
Lemma lem99563 (m : nat) (d : nat) : (term23 m d) = (term24 m d).
Proof. exact (@lem99562 m d). Qed.
Lemma lem99564 (n : nat) : (term120 n) = (term120 n).
Proof. exact (eq_refl (term120 n)). Qed.
Lemma lem99565 (n : nat) (m : nat) (d : nat) : ((S n) = (term23 m d)) = ((S n) = (term24 m d)).
Proof. exact (MK_COMB (@lem99564 n) (@lem99563 m d)). Qed.
Lemma lem99567 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem99115 m n) (@lem99114 m n)). Qed.
Lemma lem99568 (n : nat) (m : nat) (d : nat) : ((S n) = (term24 m d)) = (n = (Nat.add m d)).
Proof. exact (@lem99567 n (Nat.add m d)). Qed.
Lemma lem99571 (n : nat) (m : nat) (d : nat) : ((S n) = (term23 m d)) = (n = (Nat.add m d)).
Proof. exact (TRANS (@lem99565 n m d) (@lem99568 n m d)). Qed.
Lemma lem99572 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem99573 (n : nat) (m : nat) (d : nat) : (term178 n m d) = (term179 n m d).
Proof. exact (MK_COMB (@lem99572) (@lem99571 n m d)). Qed.
Lemma lem99584 (n : nat) (m : nat) : (term89 n m) = (term89 n m).
Proof. exact (eq_refl (term89 n m)). Qed.
Lemma lem99585 (d : nat) (n : nat) (m : nat) : (term161 d n m) = (term180 d n m).
Proof. exact (MK_COMB (@lem99573 n m d) (@lem99584 n m)). Qed.
Lemma lem99590 (d : nat) (n : nat) (m : nat) : (term180 d n m) = (term161 d n m).
Proof. exact (SYM (@lem99585 d n m)). Qed.
Lemma lem99591 (n : nat) (m : nat) (h1 : (S n) = m) : (S n) = m.
Proof. exact (h1). Qed.
Lemma lem99592 (n : nat) (m : nat) : (term181 n m) = (term181 n m).
Proof. exact (eq_refl (term181 n m)). Qed.
Lemma lem99593 (n : nat) (m : nat) (h1 : (S n) = m) : (term182 m n) = (term183 n m).
Proof. exact (MK_COMB (@lem99592 n m) (@lem99591 n m h1)). Qed.
Lemma lem99594 (n : nat) (m : nat) : (term183 n m) = (term184 n m).
Proof. exact (eq_refl (term183 n m)). Qed.
Lemma lem99595 (m : nat) (n : nat) : (term185 m n) = (term185 m n).
Proof. exact (eq_refl (term185 m n)). Qed.
Lemma lem99596 (n : nat) (m : nat) : ((term182 m n) = (term183 n m)) = ((term182 m n) = (term184 n m)).
Proof. exact (MK_COMB (@lem99595 m n) (@lem99594 n m)). Qed.
Lemma lem99597 (n : nat) (m : nat) : (term182 m n) = (term89 n m).
Proof. exact (eq_refl (term182 m n)). Qed.
Lemma lem99598 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem99599 (n : nat) (m : nat) : (term185 m n) = (term91 n m).
Proof. exact (MK_COMB (@lem99598) (@lem99597 n m)). Qed.
Lemma lem99600 (n : nat) (m : nat) : (term184 n m) = (term184 n m).
Proof. exact (eq_refl (term184 n m)). Qed.
Lemma lem99601 (n : nat) (m : nat) : ((term182 m n) = (term184 n m)) = ((term89 n m) = (term184 n m)).
Proof. exact (MK_COMB (@lem99599 n m) (@lem99600 n m)). Qed.
Lemma lem99602 (n : nat) (m : nat) : ((term182 m n) = (term183 n m)) = ((term89 n m) = (term184 n m)).
Proof. exact (TRANS (@lem99596 n m) (@lem99601 n m)). Qed.
Lemma lem99603 (n : nat) (m : nat) (h1 : (S n) = m) : (term89 n m) = (term184 n m).
Proof. exact (EQ_MP (@lem99602 n m) (@lem99593 n m h1)). Qed.
Lemma lem99604 (n : nat) (m : nat) (h1 : (S n) = m) : (term184 n m) = (term89 n m).
Proof. exact (SYM (@lem99603 n m h1)). Qed.
Lemma lem99605 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem99606 (m : nat) : (term186 m) = (term186 m).
Proof. exact (eq_refl (term186 m)). Qed.
Lemma lem99607 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term187 m n) = (term188 m d).
Proof. exact (MK_COMB (@lem99606 m) (@lem99605 n m d h1)). Qed.
Lemma lem99608 (d : nat) (m : nat) : (term188 m d) = (term189 d m).
Proof. exact (eq_refl (term188 m d)). Qed.
Lemma lem99609 (m : nat) (n : nat) : (term190 m n) = (term190 m n).
Proof. exact (eq_refl (term190 m n)). Qed.
Lemma lem99610 (n : nat) (d : nat) (m : nat) : ((term187 m n) = (term188 m d)) = ((term187 m n) = (term189 d m)).
Proof. exact (MK_COMB (@lem99609 m n) (@lem99608 d m)). Qed.
Lemma lem99611 (n : nat) (m : nat) : (term187 m n) = (term89 n m).
Proof. exact (eq_refl (term187 m n)). Qed.
Lemma lem99612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem99613 (n : nat) (m : nat) : (term190 m n) = (term91 n m).
Proof. exact (MK_COMB (@lem99612) (@lem99611 n m)). Qed.
Lemma lem99614 (d : nat) (m : nat) : (term189 d m) = (term189 d m).
Proof. exact (eq_refl (term189 d m)). Qed.
Lemma lem99615 (n : nat) (d : nat) (m : nat) : ((term187 m n) = (term189 d m)) = ((term89 n m) = (term189 d m)).
Proof. exact (MK_COMB (@lem99613 n m) (@lem99614 d m)). Qed.
Lemma lem99616 (n : nat) (d : nat) (m : nat) : ((term187 m n) = (term188 m d)) = ((term89 n m) = (term189 d m)).
Proof. exact (TRANS (@lem99610 n d m) (@lem99615 n d m)). Qed.
Lemma lem99617 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term89 n m) = (term189 d m).
Proof. exact (EQ_MP (@lem99616 n d m) (@lem99607 n m d h1)). Qed.
Lemma lem99618 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term189 d m) = (term89 n m).
Proof. exact (SYM (@lem99617 n m d h1)). Qed.
Lemma lem99622 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem99623 (x : nat) : (x = x) = True.
Proof. exact (@lem99622 nat x). Qed.
Lemma lem99624 (m : nat) : (m = m) = True.
Proof. exact (@lem99623 m). Qed.
Lemma lem99625 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem99626 (m : nat) : (term191 m) = (or True).
Proof. exact (MK_COMB (@lem99625) (@lem99624 m)). Qed.
Lemma lem99633 (n : nat) (m : nat) : (term59 n m) = (term59 n m).
Proof. exact (eq_refl (term59 n m)). Qed.
Lemma lem99634 (n : nat) (m : nat) : (term184 n m) = (term192 n m).
Proof. exact (MK_COMB (@lem99626 m) (@lem99633 n m)). Qed.
Lemma lem99636 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem99637 (n : nat) (m : nat) : (term192 n m) = True.
Proof. exact (@lem99636 (term59 n m)). Qed.
Lemma lem99638 (n : nat) (m : nat) : (term184 n m) = True.
Proof. exact (TRANS (@lem99634 n m) (@lem99637 n m)). Qed.
Lemma lem99639 (n : nat) (m : nat) : True = (term184 n m).
Proof. exact (SYM (@lem99638 n m)). Qed.
Lemma lem99640 (n : nat) (m : nat) : term184 n m.
Proof. exact (EQ_MP (@lem99639 n m) (@lem0)). Qed.
Lemma lem99660 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem99109 m n p) (@lem99108 m n p)). Qed.
Lemma lem99661 (m : nat) (d : nat) (d' : nat) : ((Nat.add m d) = (Nat.add m d')) = (d = d').
Proof. exact (@lem99660 m d d'). Qed.
Lemma lem99664 (m : nat) (d : nat) : (term193 d m) = (term194 d).
Proof. exact (fun_ext (fun d' : nat => @lem99661 m d d')). Qed.
Lemma lem99665 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem99666 (m : nat) (d : nat) : (term195 d m) = (term196 d).
Proof. exact (MK_COMB (@lem99665) (@lem99664 m d)). Qed.
Lemma lem99668 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem99100 A a) (@lem99099 A a)). Qed.
Lemma lem99669 (a : nat) : (term196 a) = True.
Proof. exact (@lem99668 nat a). Qed.
Lemma lem99670 (d : nat) : (term196 d) = True.
Proof. exact (@lem99669 d). Qed.
Lemma lem99671 (d : nat) (m : nat) : (term195 d m) = True.
Proof. exact (TRANS (@lem99666 m d) (@lem99670 d)). Qed.
Lemma lem99672 (d : nat) (m : nat) : True = (term195 d m).
Proof. exact (SYM (@lem99671 d m)). Qed.
Lemma lem99673 (d : nat) (m : nat) : term195 d m.
Proof. exact (EQ_MP (@lem99672 d m) (@lem0)). Qed.
Lemma lem99675 (d : nat) (m : nat) : term189 d m.
Proof. exact (or_intro2 (m = (term24 m d)) (@lem99673 d m)). Qed.
Lemma lem99676 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : term89 n m.
Proof. exact (EQ_MP (@lem99618 n m d h1) (@lem99675 d m)). Qed.
Lemma lem99677 (d : nat) (n : nat) (m : nat) : term180 d n m.
Proof. exact (fun h0 : n = (Nat.add m d) => @lem99676 n m d h0). Qed.
Lemma lem99678 (n : nat) (m : nat) (h1 : (S n) = m) : term89 n m.
Proof. exact (EQ_MP (@lem99604 n m h1) (@lem99640 n m)). Qed.
Lemma lem99679 (n : nat) (m : nat) : term177 n m.
Proof. exact (fun h0 : (S n) = m => @lem99678 n m h0). Qed.
Lemma lem99680 (d : nat) (n : nat) (m : nat) : term161 d n m.
Proof. exact (EQ_MP (@lem99590 d n m) (@lem99677 d n m)). Qed.
Lemma lem99681 (n : nat) (m : nat) : term154 n m.
Proof. exact (EQ_MP (@lem99554 n m) (@lem99679 n m)). Qed.
Lemma lem99682 (d : nat) (n : nat) (m : nat) : term163 d n m.
Proof. exact (fun h0 : term148 d n m => @lem99680 d n m). Qed.
Lemma lem99687 (n : nat) (m : nat) : term167 n m.
Proof. exact (fun d : nat => @lem99682 d n m). Qed.
Lemma lem99688 (n : nat) (m : nat) : term169 n m.
Proof. exact (conj (@lem99681 n m) (@lem99687 n m)). Qed.
Lemma lem99689 (n : nat) (m : nat) : term151 n m.
Proof. exact (@lem99522 n m (@lem99688 n m)). Qed.
Lemma lem99690 (n : nat) (m : nat) : term142 n m.
Proof. exact (EQ_MP (@lem99499 n m) (@lem99689 n m)). Qed.
Lemma lem99691 (n : nat) (m : nat) : term197 n m.
Proof. exact (conj (@lem99474 n m) (@lem99690 n m)). Qed.
Lemma lem99692 (n : nat) (m : nat) : (term197 n m) = ((term89 n m) = (term64 n m)).
Proof. exact (@lem32 (term89 n m) (term64 n m)). Qed.
Lemma lem99693 (n : nat) (m : nat) : (term89 n m) = (term64 n m).
Proof. exact (EQ_MP (@lem99692 n m) (@lem99691 n m)). Qed.
Lemma lem99694 (n : nat) (m : nat) (h1 : (Peano.le m n) = (term59 n m)) : (term63 m n) = (term64 n m).
Proof. exact (EQ_MP (@lem99320 n m h1) (@lem99693 n m)). Qed.
Lemma lem99695 (m : nat) : (term54 m) = (term55 m).
Proof. exact (EQ_MP (@lem99275 m) (@lem99400 m)). Qed.
Lemma lem99696 (n : nat) (m : nat) : term66 n m.
Proof. exact (fun h0 : (Peano.le m n) = (term59 n m) => @lem99694 n m h0). Qed.
Lemma lem99701 (m : nat) : term70 m.
Proof. exact (fun n : nat => @lem99696 n m). Qed.
Lemma lem99702 (m : nat) : term72 m.
Proof. exact (conj (@lem99695 m) (@lem99701 m)). Qed.
Lemma lem99703 (m : nat) : term77 m.
Proof. exact (@lem99244 m (@lem99702 m)). Qed.
Lemma lem99708 : term198.
Proof. exact (fun m : nat => @lem99703 m). Qed.
