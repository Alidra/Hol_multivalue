Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2595336_term_abbrevs.
Require Import AND_FORALL_THM_spec.
Require Import INT_DIVMOD_UNIQ_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482678_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982735_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm2318495_spec.
Require Import thm2318496_spec.
Require Import thm2318497_spec.
Require Import thm2318514_spec.
Require Import thm2318515_spec.
Require Import thm2318532_spec.
Require Import thm2318533_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem2594167 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem2594168 (m : int) (h1 : term0) : term1 m.
Proof. exact (@lem2594167 h1 m). Qed.
Lemma lem2594169 (m : int) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem2594170 (m : int) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem2594169 m) (@lem2594168 m h1)). Qed.
Lemma lem2594171 (m : int) (n : int) (h1 : term0) : term3 m n.
Proof. exact (@lem2594170 m h1 n). Qed.
Lemma lem2594172 (m : int) (n : int) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2594173 (m : int) (n : int) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem2594172 m n) (@lem2594171 m n h1)). Qed.
Lemma lem2594174 (m : int) (n : int) (q : int) (h1 : term0) : term5 m n q.
Proof. exact (@lem2594173 m n h1 q). Qed.
Lemma lem2594175 (q : int) (m : int) (n : int) : (term5 m n q) = (term6 q m n).
Proof. exact (eq_refl (term5 m n q)). Qed.
Lemma lem2594176 (q : int) (m : int) (n : int) (h1 : term0) : term6 q m n.
Proof. exact (EQ_MP (@lem2594175 q m n) (@lem2594174 m n q h1)). Qed.
Lemma lem2594177 (q : int) (m : int) (n : int) (r : int) (h1 : term0) : term7 q m n r.
Proof. exact (@lem2594176 q m n h1 r). Qed.
Lemma lem2594178 (q : int) (m : int) (n : int) (r : int) : (term7 q m n r) = (term8 q m n r).
Proof. exact (eq_refl (term7 q m n r)). Qed.
Lemma lem2594179 (q : int) (m : int) (n : int) (r : int) (h1 : term0) : term8 q m n r.
Proof. exact (EQ_MP (@lem2594178 q m n r) (@lem2594177 q m n r h1)). Qed.
Lemma lem2594180 (m : int) (q : int) (r : int) (n : int) (h1 : term9 m q r n) : term9 m q r n.
Proof. exact (h1). Qed.
Lemma lem2594181 (m : int) (q : int) (r : int) (n : int) (h1 : term0) (h2 : term9 m q r n) : term10 q m n r.
Proof. exact (@lem2594179 q m n r h1 (@lem2594180 m q r n h2)). Qed.
Lemma lem2594182 (m : int) (q : int) (r : int) (n : int) (h1 : term9 m q r n) : term11 q m n r.
Proof. exact (fun h0 : term0 => @lem2594181 m q r n h0 h1). Qed.
Lemma lem2594183 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem2594184 (m : int) (q : int) (r : int) (n : int) (h1 : term0) (h2 : term9 m q r n) : term10 q m n r.
Proof. exact (@lem2594182 m q r n h2 (@lem2594183 h1)). Qed.
Lemma lem2594185 (q : int) (m : int) (n : int) (r : int) (h1 : term0) : term8 q m n r.
Proof. exact (fun h0 : term9 m q r n => @lem2594184 m q r n h1 h0). Qed.
Lemma lem2594186 (q : int) (m : int) (n : int) (h1 : term0) : term6 q m n.
Proof. exact (fun r : int => @lem2594185 q m n r h1). Qed.
Lemma lem2594187 (q : int) (m : int) (h1 : term0) : term12 q m.
Proof. exact (fun n : int => @lem2594186 q m n h1). Qed.
Lemma lem2594188 (q : int) (h1 : term0) : term13 q.
Proof. exact (fun m : int => @lem2594187 q m h1). Qed.
Lemma lem2594189 (h1 : term0) : term14.
Proof. exact (fun q : int => @lem2594188 q h1). Qed.
Lemma lem2594190 : term15.
Proof. exact (fun h0 : term0 => @lem2594189 h0). Qed.
Lemma lem2594191 : term14.
Proof. exact (@lem2594190 (@lem2495588)). Qed.
Lemma lem2594192 (q : int) : term16 q.
Proof. exact (@lem2594191 q). Qed.
Lemma lem2594193 (q : int) : (term16 q) = (term13 q).
Proof. exact (eq_refl (term16 q)). Qed.
Lemma lem2594194 (q : int) : term13 q.
Proof. exact (EQ_MP (@lem2594193 q) (@lem2594192 q)). Qed.
Lemma lem2594195 (q : int) (m : int) : term17 q m.
Proof. exact (@lem2594194 q m). Qed.
Lemma lem2594196 (q : int) (m : int) : (term17 q m) = (term12 q m).
Proof. exact (eq_refl (term17 q m)). Qed.
Lemma lem2594197 (q : int) (m : int) : term12 q m.
Proof. exact (EQ_MP (@lem2594196 q m) (@lem2594195 q m)). Qed.
Lemma lem2594198 (q : int) (m : int) (n : int) : term18 q m n.
Proof. exact (@lem2594197 q m n). Qed.
Lemma lem2594199 (q : int) (m : int) (n : int) : (term18 q m n) = (term6 q m n).
Proof. exact (eq_refl (term18 q m n)). Qed.
Lemma lem2594200 (q : int) (m : int) (n : int) : term6 q m n.
Proof. exact (EQ_MP (@lem2594199 q m n) (@lem2594198 q m n)). Qed.
Lemma lem2594201 (q : int) (m : int) (n : int) (r : int) : term7 q m n r.
Proof. exact (@lem2594200 q m n r). Qed.
Lemma lem2594202 (q : int) (m : int) (n : int) (r : int) : (term7 q m n r) = (term8 q m n r).
Proof. exact (eq_refl (term7 q m n r)). Qed.
Lemma lem2594204 {A : Type'} (P : A -> Prop) : term19 A P.
Proof. exact (@lem5146 A P). Qed.
Lemma lem2594205 {A : Type'} (P : A -> Prop) : (term19 A P) = (term20 A P).
Proof. exact (eq_refl (term19 A P)). Qed.
Lemma lem2594206 {A : Type'} (P : A -> Prop) : term20 A P.
Proof. exact (EQ_MP (@lem2594205 A P) (@lem2594204 A P)). Qed.
Lemma lem2594207 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term21 A P Q.
Proof. exact (@lem2594206 A P Q). Qed.
Lemma lem2594208 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term21 A P Q) = ((term22 A P Q) = (term23 A P Q)).
Proof. exact (eq_refl (term21 A P Q)). Qed.
Lemma lem2594211 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term22 A P Q) = (term23 A P Q).
Proof. exact (EQ_MP (@lem2594208 A P Q) (@lem2594207 A P Q)). Qed.
Lemma lem2594212 (P : int -> Prop) (Q : int -> Prop) : (term24 P Q) = (term25 P Q).
Proof. exact (@lem2594211 int P Q). Qed.
Lemma lem2594213 : term26 = term27.
Proof. exact (@lem2594212 term28 term29). Qed.
Lemma lem2594214 (n : int) : (term30 n) = ((term31 n) = n).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem2594215 : term32 = term28.
Proof. exact (fun_ext (fun n : int => @lem2594214 n)). Qed.
Lemma lem2594216 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2594217 : term33 = term34.
Proof. exact (MK_COMB (@lem2594216) (@lem2594215)). Qed.
Lemma lem2594218 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2594219 : term35 = term36.
Proof. exact (MK_COMB (@lem2594218) (@lem2594217)). Qed.
Lemma lem2594220 (n : int) : (term37 n) = ((term38 n) = term39).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem2594221 : term40 = term29.
Proof. exact (fun_ext (fun n : int => @lem2594220 n)). Qed.
Lemma lem2594222 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2594223 : term41 = term42.
Proof. exact (MK_COMB (@lem2594222) (@lem2594221)). Qed.
Lemma lem2594224 : term26 = term43.
Proof. exact (MK_COMB (@lem2594219) (@lem2594223)). Qed.
Lemma lem2594225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2594226 : term44 = term45.
Proof. exact (MK_COMB (@lem2594225) (@lem2594224)). Qed.
Lemma lem2594227 (n : int) : (term30 n) = ((term31 n) = n).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem2594228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2594229 (n : int) : (term46 n) = (term47 n).
Proof. exact (MK_COMB (@lem2594228) (@lem2594227 n)). Qed.
Lemma lem2594230 (n : int) : (term37 n) = ((term38 n) = term39).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem2594231 (n : int) : (term48 n) = (term49 n).
Proof. exact (MK_COMB (@lem2594229 n) (@lem2594230 n)). Qed.
Lemma lem2594232 : term50 = term51.
Proof. exact (fun_ext (fun n : int => @lem2594231 n)). Qed.
Lemma lem2594233 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2594234 : term27 = term52.
Proof. exact (MK_COMB (@lem2594233) (@lem2594232)). Qed.
Lemma lem2594235 : (term26 = term27) = (term43 = term52).
Proof. exact (MK_COMB (@lem2594226) (@lem2594234)). Qed.
Lemma lem2594236 : term43 = term52.
Proof. exact (EQ_MP (@lem2594235) (@lem2594213)). Qed.
Lemma lem2594247 : term52 = term43.
Proof. exact (SYM (@lem2594236)). Qed.
Lemma lem2594249 (q : int) (m : int) (n : int) (r : int) : term8 q m n r.
Proof. exact (EQ_MP (@lem2594202 q m n r) (@lem2594201 q m n r)). Qed.
Lemma lem2594250 (n : int) : term53 n.
Proof. exact (@lem2594249 n n term54 term39). Qed.
Lemma lem2594251 (n : int) : (term55 n) = (term56 n).
Proof. exact (@lem2318604 (term56 n)). Qed.
Lemma lem2594268 : term57 = term58.
Proof. exact (@lem17045 term59 term60). Qed.
Lemma lem2594270 (n : int) : (term61 n) = (term61 n).
Proof. exact (eq_refl (term61 n)). Qed.
Lemma lem2594271 (n : int) : (term62 n) = (term63 n).
Proof. exact (MK_COMB (@lem2594270 n) (@lem2594268)). Qed.
Lemma lem2594272 (n : int) : (term64 n) = (term62 n).
Proof. exact (@lem17045 (n = (term65 n)) term66). Qed.
Lemma lem2594290 (n : int) : (term64 n) = (term63 n).
Proof. exact (TRANS (@lem2594272 n) (@lem2594271 n)). Qed.
Lemma lem2594292 (y : int) (x : int) : (term67 x y) = (term68 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2594293 (n : int) : (term69 n) = (term70 n).
Proof. exact (@lem2594292 (term65 n) n). Qed.
Lemma lem2594295 (x : int) (y : int) : (int_le x y) = (term71 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2594296 (n : int) : (term72 n) = (term73 n).
Proof. exact (@lem2594295 (term74 n) (term65 n)). Qed.
Lemma lem2594298 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2594299 (n : int) : (term77 n) = (term78 n).
Proof. exact (@lem2594298 n term54). Qed.
Lemma lem2594301 (n : nat) : (term79 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2594302 : term80 = term81.
Proof. exact (@lem2594301 term82). Qed.
Lemma lem2594303 (n : int) : (term83 n) = (term83 n).
Proof. exact (eq_refl (term83 n)). Qed.
Lemma lem2594304 (n : int) : (term78 n) = (term84 n).
Proof. exact (MK_COMB (@lem2594303 n) (@lem2594302)). Qed.
Lemma lem2594305 (n : int) : (term77 n) = (term84 n).
Proof. exact (TRANS (@lem2594299 n) (@lem2594304 n)). Qed.
Lemma lem2594306 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2594307 (n : int) : (term85 n) = (term86 n).
Proof. exact (MK_COMB (@lem2594306) (@lem2594305 n)). Qed.
Lemma lem2594309 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2594310 (n : int) : (term87 n) = (term88 n).
Proof. exact (@lem2594309 (term89 n) term39). Qed.
Lemma lem2594312 (x : int) (y : int) : (term90 x y) = (term91 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2594313 (n : int) : (term92 n) = (term93 n).
Proof. exact (@lem2594312 n term54). Qed.
Lemma lem2594315 (n : nat) : (term79 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2594316 : term80 = term81.
Proof. exact (@lem2594315 term82). Qed.
Lemma lem2594317 (n : int) : (term94 n) = (term94 n).
Proof. exact (eq_refl (term94 n)). Qed.
Lemma lem2594318 (n : int) : (term93 n) = (term95 n).
Proof. exact (MK_COMB (@lem2594317 n) (@lem2594316)). Qed.
Lemma lem2594319 (n : int) : (term92 n) = (term95 n).
Proof. exact (TRANS (@lem2594313 n) (@lem2594318 n)). Qed.
Lemma lem2594320 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2594321 (n : int) : (term96 n) = (term97 n).
Proof. exact (MK_COMB (@lem2594320) (@lem2594319 n)). Qed.
Lemma lem2594323 (n : nat) : (term79 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2594324 : term98 = term99.
Proof. exact (@lem2594323 (NUMERAL 0)). Qed.
Lemma lem2594325 (n : int) : (term88 n) = (term100 n).
Proof. exact (MK_COMB (@lem2594321 n) (@lem2594324)). Qed.
Lemma lem2594326 (n : int) : (term87 n) = (term100 n).
Proof. exact (TRANS (@lem2594310 n) (@lem2594325 n)). Qed.
Lemma lem2594327 (n : int) : (term73 n) = (term101 n).
Proof. exact (MK_COMB (@lem2594307 n) (@lem2594326 n)). Qed.
Lemma lem2594328 (n : int) : (term72 n) = (term101 n).
Proof. exact (TRANS (@lem2594296 n) (@lem2594327 n)). Qed.
Lemma lem2594329 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2594330 (n : int) : (term102 n) = (term103 n).
Proof. exact (MK_COMB (@lem2594329) (@lem2594328 n)). Qed.
Lemma lem2594332 (x : int) (y : int) : (int_le x y) = (term71 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2594333 (n : int) : (term104 n) = (term105 n).
Proof. exact (@lem2594332 (term106 n) n). Qed.
Lemma lem2594335 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2594336 (n : int) : (term107 n) = (term108 n).
Proof. exact (@lem2594335 (term65 n) term54). Qed.
Lemma lem2594338 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2594339 (n : int) : (term87 n) = (term88 n).
Proof. exact (@lem2594338 (term89 n) term39). Qed.
Lemma lem2594341 (x : int) (y : int) : (term90 x y) = (term91 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2594342 (n : int) : (term92 n) = (term93 n).
Proof. exact (@lem2594341 n term54). Qed.
Lemma lem2594344 (n : nat) : (term79 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2594345 : term80 = term81.
Proof. exact (@lem2594344 term82). Qed.
Lemma lem2594346 (n : int) : (term94 n) = (term94 n).
Proof. exact (eq_refl (term94 n)). Qed.
Lemma lem2594347 (n : int) : (term93 n) = (term95 n).
Proof. exact (MK_COMB (@lem2594346 n) (@lem2594345)). Qed.
Lemma lem2594348 (n : int) : (term92 n) = (term95 n).
Proof. exact (TRANS (@lem2594342 n) (@lem2594347 n)). Qed.
Lemma lem2594349 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2594350 (n : int) : (term96 n) = (term97 n).
Proof. exact (MK_COMB (@lem2594349) (@lem2594348 n)). Qed.
Lemma lem2594352 (n : nat) : (term79 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2594353 : term98 = term99.
Proof. exact (@lem2594352 (NUMERAL 0)). Qed.
Lemma lem2594354 (n : int) : (term88 n) = (term100 n).
Proof. exact (MK_COMB (@lem2594350 n) (@lem2594353)). Qed.
Lemma lem2594355 (n : int) : (term87 n) = (term100 n).
Proof. exact (TRANS (@lem2594339 n) (@lem2594354 n)). Qed.
Lemma lem2594356 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2594357 (n : int) : (term109 n) = (term110 n).
Proof. exact (MK_COMB (@lem2594356) (@lem2594355 n)). Qed.
Lemma lem2594359 (n : nat) : (term79 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2594360 : term80 = term81.
Proof. exact (@lem2594359 term82). Qed.
Lemma lem2594361 (n : int) : (term108 n) = (term111 n).
Proof. exact (MK_COMB (@lem2594357 n) (@lem2594360)). Qed.
Lemma lem2594362 (n : int) : (term107 n) = (term111 n).
Proof. exact (TRANS (@lem2594336 n) (@lem2594361 n)). Qed.
Lemma lem2594363 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2594364 (n : int) : (term112 n) = (term113 n).
Proof. exact (MK_COMB (@lem2594363) (@lem2594362 n)). Qed.
Lemma lem2594365 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2594366 (n : int) : (term105 n) = (term114 n).
Proof. exact (MK_COMB (@lem2594364 n) (@lem2594365 n)). Qed.
Lemma lem2594367 (n : int) : (term104 n) = (term114 n).
Proof. exact (TRANS (@lem2594333 n) (@lem2594366 n)). Qed.
Lemma lem2594368 (n : int) : (term70 n) = (term115 n).
Proof. exact (MK_COMB (@lem2594330 n) (@lem2594367 n)). Qed.
Lemma lem2594369 (n : int) : (term69 n) = (term115 n).
Proof. exact (TRANS (@lem2594293 n) (@lem2594368 n)). Qed.
Lemma lem2594371 (y : int) (x : int) : (term116 x y) = (term117 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2594372 : term118 = term119.
Proof. exact (@lem2594371 term39 term39). Qed.
Lemma lem2594374 (x : int) (y : int) : (int_le x y) = (term71 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2594375 : term119 = term120.
Proof. exact (@lem2594374 term121 term39). Qed.
Lemma lem2594377 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2594378 : term122 = term123.
Proof. exact (@lem2594377 term39 term54). Qed.
Lemma lem2594380 (n : nat) : (term79 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2594381 : term98 = term99.
Proof. exact (@lem2594380 (NUMERAL 0)). Qed.
Lemma lem2594382 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2594383 : term124 = term125.
Proof. exact (MK_COMB (@lem2594382) (@lem2594381)). Qed.
Lemma lem2594385 (n : nat) : (term79 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2594386 : term80 = term81.
Proof. exact (@lem2594385 term82). Qed.
Lemma lem2594387 : term123 = term126.
Proof. exact (MK_COMB (@lem2594383) (@lem2594386)). Qed.
Lemma lem2594388 : term122 = term126.
Proof. exact (TRANS (@lem2594378) (@lem2594387)). Qed.
Lemma lem2594389 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2594390 : term127 = term128.
Proof. exact (MK_COMB (@lem2594389) (@lem2594388)). Qed.
Lemma lem2594392 (n : nat) : (term79 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2594393 : term98 = term99.
Proof. exact (@lem2594392 (NUMERAL 0)). Qed.
Lemma lem2594394 : term120 = term129.
Proof. exact (MK_COMB (@lem2594390) (@lem2594393)). Qed.
Lemma lem2594395 : term119 = term129.
Proof. exact (TRANS (@lem2594375) (@lem2594394)). Qed.
Lemma lem2594396 : term118 = term129.
Proof. exact (TRANS (@lem2594372) (@lem2594395)). Qed.
Lemma lem2594398 (y : int) (x : int) : (term130 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem2594399 : term131 = term132.
Proof. exact (@lem2594398 term133 term39). Qed.
Lemma lem2594401 (x : int) (y : int) : (int_le x y) = (term71 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2594402 : term132 = term134.
Proof. exact (@lem2594401 term133 term39). Qed.
Lemma lem2594404 (x : int) : (term135 x) = (term136 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2594405 : term137 = term138.
Proof. exact (@lem2594404 term54). Qed.
Lemma lem2594407 (n : nat) : (term79 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2594408 : term80 = term81.
Proof. exact (@lem2594407 term82). Qed.
Lemma lem2594409 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2594410 : term138 = term139.
Proof. exact (MK_COMB (@lem2594409) (@lem2594408)). Qed.
Lemma lem2594411 : term137 = term139.
Proof. exact (TRANS (@lem2594405) (@lem2594410)). Qed.
Lemma lem2594412 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2594413 : term140 = term141.
Proof. exact (MK_COMB (@lem2594412) (@lem2594411)). Qed.
Lemma lem2594415 (n : nat) : (term79 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2594416 : term98 = term99.
Proof. exact (@lem2594415 (NUMERAL 0)). Qed.
Lemma lem2594417 : term134 = term142.
Proof. exact (MK_COMB (@lem2594413) (@lem2594416)). Qed.
Lemma lem2594418 : term132 = term142.
Proof. exact (TRANS (@lem2594402) (@lem2594417)). Qed.
Lemma lem2594419 : term131 = term142.
Proof. exact (TRANS (@lem2594399) (@lem2594418)). Qed.
Lemma lem2594420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2594421 : term143 = term144.
Proof. exact (MK_COMB (@lem2594420) (@lem2594396)). Qed.
Lemma lem2594422 : term58 = term145.
Proof. exact (MK_COMB (@lem2594421) (@lem2594419)). Qed.
Lemma lem2594423 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2594424 (n : int) : (term61 n) = (term146 n).
Proof. exact (MK_COMB (@lem2594423) (@lem2594369 n)). Qed.
Lemma lem2594425 (n : int) : (term63 n) = (term147 n).
Proof. exact (MK_COMB (@lem2594424 n) (@lem2594422)). Qed.
Lemma lem2594426 (n : int) : (term64 n) = (term147 n).
Proof. exact (TRANS (@lem2594290 n) (@lem2594425 n)). Qed.
Lemma lem2594430 (t : Prop) : (term148 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2594466 (n : int) : (term149 n) = (term147 n).
Proof. exact (@lem2594430 (term147 n)). Qed.
Lemma lem2594467 (n : int) : (term101 n) = (term150 n).
Proof. exact (@lem1988287 (term100 n) (term84 n)). Qed.
Lemma lem2594474 (n : int) : (term84 n) = (term84 n).
Proof. exact (eq_refl (term84 n)). Qed.
Lemma lem2594475 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem2594482 (n : int) : (term95 n) = (real_of_int n).
Proof. exact (@lem1982735 (real_of_int n)). Qed.
Lemma lem2594483 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2594484 (n : int) : (term97 n) = (term83 n).
Proof. exact (MK_COMB (@lem2594483) (@lem2594482 n)). Qed.
Lemma lem2594485 (n : int) : (term100 n) = (term151 n).
Proof. exact (MK_COMB (@lem2594484 n) (@lem2594475)). Qed.
Lemma lem2594486 (n : int) : (term151 n) = (real_of_int n).
Proof. exact (@lem1982723 (real_of_int n)). Qed.
Lemma lem2594487 (n : int) : (term100 n) = (real_of_int n).
Proof. exact (TRANS (@lem2594485 n) (@lem2594486 n)). Qed.
Lemma lem2594488 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2594489 (n : int) : (term152 n) = (term153 n).
Proof. exact (MK_COMB (@lem2594488) (@lem2594487 n)). Qed.
Lemma lem2594490 (n : int) : (term154 n) = (term155 n).
Proof. exact (MK_COMB (@lem2594489 n) (@lem2594474 n)). Qed.
Lemma lem2594491 (n : int) : (term155 n) = (term156 n).
Proof. exact (@lem1982792 (real_of_int n) (term84 n)). Qed.
Lemma lem2594492 (n : int) : (term157 n) = (term158 n).
Proof. exact (@lem1982781 (real_of_int n) term159 term81). Qed.
Lemma lem2594494 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2594495 : term81 = term161.
Proof. exact (@lem2594494 term82). Qed.
Lemma lem2594497 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2594498 : term159 = term164.
Proof. exact (@lem2594497 term82). Qed.
Lemma lem2594499 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2594500 : term165 = term166.
Proof. exact (MK_COMB (@lem2594499) (@lem2594498)). Qed.
Lemma lem2594501 : term167 = term168.
Proof. exact (MK_COMB (@lem2594500) (@lem2594495)). Qed.
Lemma lem2594502 : term168 = term169.
Proof. exact (@lem1981613 term159 term81 term81 term81). Qed.
Lemma lem2594504 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2594505 : term172 = term173.
Proof. exact (@lem2594504 term82 term82). Qed.
Lemma lem2594506 : (term174 = (BIT1 0)) = (term175 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2594507 : term175 = term82.
Proof. exact (EQ_MP (@lem2594506) (@lem940073)). Qed.
Lemma lem2594508 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2594509 : term173 = term81.
Proof. exact (MK_COMB (@lem2594508) (@lem2594507)). Qed.
Lemma lem2594510 : term172 = term81.
Proof. exact (TRANS (@lem2594505) (@lem2594509)). Qed.
Lemma lem2594512 (m : nat) (n : nat) : (term176 m n) = (term177 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2594513 : term167 = term178.
Proof. exact (@lem2594512 term82 term82). Qed.
Lemma lem2594514 : (term174 = (BIT1 0)) = (term175 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2594515 : term175 = term82.
Proof. exact (EQ_MP (@lem2594514) (@lem940073)). Qed.
Lemma lem2594516 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2594517 : term173 = term81.
Proof. exact (MK_COMB (@lem2594516) (@lem2594515)). Qed.
Lemma lem2594518 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2594519 : term178 = term159.
Proof. exact (MK_COMB (@lem2594518) (@lem2594517)). Qed.
Lemma lem2594520 : term167 = term159.
Proof. exact (TRANS (@lem2594513) (@lem2594519)). Qed.
Lemma lem2594521 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2594522 : term179 = term180.
Proof. exact (MK_COMB (@lem2594521) (@lem2594520)). Qed.
Lemma lem2594523 : term169 = term164.
Proof. exact (MK_COMB (@lem2594522) (@lem2594510)). Qed.
Lemma lem2594524 : term168 = term164.
Proof. exact (TRANS (@lem2594502) (@lem2594523)). Qed.
Lemma lem2594525 : term167 = term164.
Proof. exact (TRANS (@lem2594501) (@lem2594524)). Qed.
Lemma lem2594527 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2594528 : term164 = term159.
Proof. exact (@lem2594527 term159). Qed.
Lemma lem2594529 : term167 = term159.
Proof. exact (TRANS (@lem2594525) (@lem2594528)). Qed.
Lemma lem2594532 (n : int) : (term182 n) = (term182 n).
Proof. exact (eq_refl (term182 n)). Qed.
Lemma lem2594533 (n : int) : (term158 n) = (term183 n).
Proof. exact (MK_COMB (@lem2594532 n) (@lem2594529)). Qed.
Lemma lem2594534 (n : int) : (term157 n) = (term183 n).
Proof. exact (TRANS (@lem2594492 n) (@lem2594533 n)). Qed.
Lemma lem2594535 (n : int) : (term83 n) = (term83 n).
Proof. exact (eq_refl (term83 n)). Qed.
Lemma lem2594536 (n : int) : (term156 n) = (term184 n).
Proof. exact (MK_COMB (@lem2594535 n) (@lem2594534 n)). Qed.
Lemma lem2594537 (n : int) : (term184 n) = (term185 n).
Proof. exact (@lem1982763 (real_of_int n) (term186 n) term159). Qed.
Lemma lem2594538 (n : int) : (term187 n) = (term188 n).
Proof. exact (@lem1982715 term159 (real_of_int n)). Qed.
Lemma lem2594540 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2594541 : term81 = term161.
Proof. exact (@lem2594540 term82). Qed.
Lemma lem2594543 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2594544 : term159 = term164.
Proof. exact (@lem2594543 term82). Qed.
Lemma lem2594545 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2594546 : term189 = term190.
Proof. exact (MK_COMB (@lem2594545) (@lem2594544)). Qed.
Lemma lem2594547 : term191 = term192.
Proof. exact (MK_COMB (@lem2594546) (@lem2594541)). Qed.
Lemma lem2594548 : term193.
Proof. exact (@lem1981473 term159 term81 term81 term81 term99 term81). Qed.
Lemma lem2594550 (m : nat) (n : nat) : (term194 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2594551 : term195 = term196.
Proof. exact (@lem2594550 (NUMERAL 0) term82). Qed.
Lemma lem2594552 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2594553 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2594554 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2594553 h1) (fun h1 : term196 = True => @lem2594552)). Qed.
Lemma lem2594555 : term196 = True.
Proof. exact (EQ_MP (@lem2594554) (@lem2594552)). Qed.
Lemma lem2594556 : term195 = True.
Proof. exact (TRANS (@lem2594551) (@lem2594555)). Qed.
Lemma lem2594557 : True = term195.
Proof. exact (SYM (@lem2594556)). Qed.
Lemma lem2594558 : term195.
Proof. exact (EQ_MP (@lem2594557) (@lem0)). Qed.
Lemma lem2594559 : term198.
Proof. exact (@lem2594548 (@lem2594558)). Qed.
Lemma lem2594561 (m : nat) (n : nat) : (term194 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2594562 : term195 = term196.
Proof. exact (@lem2594561 (NUMERAL 0) term82). Qed.
Lemma lem2594563 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2594564 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2594565 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2594564 h1) (fun h1 : term196 = True => @lem2594563)). Qed.
Lemma lem2594566 : term196 = True.
Proof. exact (EQ_MP (@lem2594565) (@lem2594563)). Qed.
Lemma lem2594567 : term195 = True.
Proof. exact (TRANS (@lem2594562) (@lem2594566)). Qed.
Lemma lem2594568 : True = term195.
Proof. exact (SYM (@lem2594567)). Qed.
Lemma lem2594569 : term195.
Proof. exact (EQ_MP (@lem2594568) (@lem0)). Qed.
Lemma lem2594570 : term199.
Proof. exact (@lem2594559 (@lem2594569)). Qed.
Lemma lem2594572 (m : nat) (n : nat) : (term194 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2594573 : term195 = term196.
Proof. exact (@lem2594572 (NUMERAL 0) term82). Qed.
Lemma lem2594574 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2594575 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2594576 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2594575 h1) (fun h1 : term196 = True => @lem2594574)). Qed.
Lemma lem2594577 : term196 = True.
Proof. exact (EQ_MP (@lem2594576) (@lem2594574)). Qed.
Lemma lem2594578 : term195 = True.
Proof. exact (TRANS (@lem2594573) (@lem2594577)). Qed.
Lemma lem2594579 : True = term195.
Proof. exact (SYM (@lem2594578)). Qed.
Lemma lem2594580 : term195.
Proof. exact (EQ_MP (@lem2594579) (@lem0)). Qed.
Lemma lem2594581 : term200.
Proof. exact (@lem2594570 (@lem2594580)). Qed.
Lemma lem2594583 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2594584 : term172 = term173.
Proof. exact (@lem2594583 term82 term82). Qed.
Lemma lem2594585 : (term174 = (BIT1 0)) = (term175 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2594586 : term175 = term82.
Proof. exact (EQ_MP (@lem2594585) (@lem940073)). Qed.
Lemma lem2594587 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2594588 : term173 = term81.
Proof. exact (MK_COMB (@lem2594587) (@lem2594586)). Qed.
Lemma lem2594589 : term172 = term81.
Proof. exact (TRANS (@lem2594584) (@lem2594588)). Qed.
Lemma lem2594591 (m : nat) (n : nat) : (term176 m n) = (term177 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2594592 : term167 = term178.
Proof. exact (@lem2594591 term82 term82). Qed.
Lemma lem2594593 : (term174 = (BIT1 0)) = (term175 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2594594 : term175 = term82.
Proof. exact (EQ_MP (@lem2594593) (@lem940073)). Qed.
Lemma lem2594595 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2594596 : term173 = term81.
Proof. exact (MK_COMB (@lem2594595) (@lem2594594)). Qed.
Lemma lem2594597 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2594598 : term178 = term159.
Proof. exact (MK_COMB (@lem2594597) (@lem2594596)). Qed.
Lemma lem2594599 : term167 = term159.
Proof. exact (TRANS (@lem2594592) (@lem2594598)). Qed.
Lemma lem2594600 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2594601 : term201 = term189.
Proof. exact (MK_COMB (@lem2594600) (@lem2594599)). Qed.
Lemma lem2594602 : term202 = term191.
Proof. exact (MK_COMB (@lem2594601) (@lem2594589)). Qed.
Lemma lem2594604 (m : nat) : (term203 m) = term99.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2594605 : term191 = term99.
Proof. exact (@lem2594604 term82). Qed.
Lemma lem2594606 : term202 = term99.
Proof. exact (TRANS (@lem2594602) (@lem2594605)). Qed.
Lemma lem2594607 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2594608 : term204 = term205.
Proof. exact (MK_COMB (@lem2594607) (@lem2594606)). Qed.
Lemma lem2594609 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2594610 : term206 = term207.
Proof. exact (MK_COMB (@lem2594608) (@lem2594609)). Qed.
Lemma lem2594612 (x : nat) : (term208 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2594613 : term207 = term99.
Proof. exact (@lem2594612 term82). Qed.
Lemma lem2594614 : term206 = term99.
Proof. exact (TRANS (@lem2594610) (@lem2594613)). Qed.
Lemma lem2594616 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2594617 : term172 = term173.
Proof. exact (@lem2594616 term82 term82). Qed.
Lemma lem2594618 : (term174 = (BIT1 0)) = (term175 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2594619 : term175 = term82.
Proof. exact (EQ_MP (@lem2594618) (@lem940073)). Qed.
Lemma lem2594620 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2594621 : term173 = term81.
Proof. exact (MK_COMB (@lem2594620) (@lem2594619)). Qed.
Lemma lem2594622 : term172 = term81.
Proof. exact (TRANS (@lem2594617) (@lem2594621)). Qed.
Lemma lem2594623 : term205 = term205.
Proof. exact (eq_refl term205). Qed.
Lemma lem2594624 : term209 = term207.
Proof. exact (MK_COMB (@lem2594623) (@lem2594622)). Qed.
Lemma lem2594626 (x : nat) : (term208 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2594627 : term207 = term99.
Proof. exact (@lem2594626 term82). Qed.
Lemma lem2594628 : term209 = term99.
Proof. exact (TRANS (@lem2594624) (@lem2594627)). Qed.
Lemma lem2594629 : term99 = term209.
Proof. exact (SYM (@lem2594628)). Qed.
Lemma lem2594630 : term206 = term209.
Proof. exact (TRANS (@lem2594614) (@lem2594629)). Qed.
Lemma lem2594631 : term192 = term210.
Proof. exact (@lem2594581 (@lem2594630)). Qed.
Lemma lem2594632 : term191 = term210.
Proof. exact (TRANS (@lem2594547) (@lem2594631)). Qed.
Lemma lem2594634 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2594635 : term210 = term99.
Proof. exact (@lem2594634 term99). Qed.
Lemma lem2594636 : term191 = term99.
Proof. exact (TRANS (@lem2594632) (@lem2594635)). Qed.
Lemma lem2594637 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2594638 : term211 = term205.
Proof. exact (MK_COMB (@lem2594637) (@lem2594636)). Qed.
Lemma lem2594639 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2594640 (n : int) : (term188 n) = (term212 n).
Proof. exact (MK_COMB (@lem2594638) (@lem2594639 n)). Qed.
Lemma lem2594641 (n : int) : (term187 n) = (term212 n).
Proof. exact (TRANS (@lem2594538 n) (@lem2594640 n)). Qed.
Lemma lem2594642 (n : int) : (term212 n) = term99.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2594643 (n : int) : (term187 n) = term99.
Proof. exact (TRANS (@lem2594641 n) (@lem2594642 n)). Qed.
Lemma lem2594644 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2594645 (n : int) : (term213 n) = term125.
Proof. exact (MK_COMB (@lem2594644) (@lem2594643 n)). Qed.
Lemma lem2594646 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2594647 (n : int) : (term185 n) = term214.
Proof. exact (MK_COMB (@lem2594645 n) (@lem2594646)). Qed.
Lemma lem2594648 (n : int) : (term184 n) = term214.
Proof. exact (TRANS (@lem2594537 n) (@lem2594647 n)). Qed.
Lemma lem2594649 : term214 = term159.
Proof. exact (@lem1982721 term159). Qed.
Lemma lem2594650 (n : int) : (term184 n) = term159.
Proof. exact (TRANS (@lem2594648 n) (@lem2594649)). Qed.
Lemma lem2594651 (n : int) : (term156 n) = term159.
Proof. exact (TRANS (@lem2594536 n) (@lem2594650 n)). Qed.
Lemma lem2594652 (n : int) : (term155 n) = term159.
Proof. exact (TRANS (@lem2594491 n) (@lem2594651 n)). Qed.
Lemma lem2594653 (n : int) : (term154 n) = term159.
Proof. exact (TRANS (@lem2594490 n) (@lem2594652 n)). Qed.
Lemma lem2594654 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2594655 (n : int) : (term215 n) = term216.
Proof. exact (MK_COMB (@lem2594654) (@lem2594653 n)). Qed.
Lemma lem2594656 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem2594657 (n : int) : (term150 n) = term217.
Proof. exact (MK_COMB (@lem2594655 n) (@lem2594656)). Qed.
Lemma lem2594658 (n : int) : (term101 n) = term217.
Proof. exact (TRANS (@lem2594467 n) (@lem2594657 n)). Qed.
Lemma lem2594659 (n : int) : (term114 n) = (term218 n).
Proof. exact (@lem1988287 (real_of_int n) (term111 n)). Qed.
Lemma lem2594660 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2594661 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem2594668 (n : int) : (term95 n) = (real_of_int n).
Proof. exact (@lem1982735 (real_of_int n)). Qed.
Lemma lem2594669 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2594670 (n : int) : (term97 n) = (term83 n).
Proof. exact (MK_COMB (@lem2594669) (@lem2594668 n)). Qed.
Lemma lem2594671 (n : int) : (term100 n) = (term151 n).
Proof. exact (MK_COMB (@lem2594670 n) (@lem2594661)). Qed.
Lemma lem2594672 (n : int) : (term151 n) = (real_of_int n).
Proof. exact (@lem1982723 (real_of_int n)). Qed.
Lemma lem2594673 (n : int) : (term100 n) = (real_of_int n).
Proof. exact (TRANS (@lem2594671 n) (@lem2594672 n)). Qed.
Lemma lem2594674 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2594675 (n : int) : (term110 n) = (term83 n).
Proof. exact (MK_COMB (@lem2594674) (@lem2594673 n)). Qed.
Lemma lem2594678 (n : int) : (term111 n) = (term84 n).
Proof. exact (MK_COMB (@lem2594675 n) (@lem2594660)). Qed.
Lemma lem2594681 (n : int) : (term153 n) = (term153 n).
Proof. exact (eq_refl (term153 n)). Qed.
Lemma lem2594682 (n : int) : (term219 n) = (term155 n).
Proof. exact (MK_COMB (@lem2594681 n) (@lem2594678 n)). Qed.
Lemma lem2594683 (n : int) : (term155 n) = (term156 n).
Proof. exact (@lem1982792 (real_of_int n) (term84 n)). Qed.
Lemma lem2594684 (n : int) : (term157 n) = (term158 n).
Proof. exact (@lem1982781 (real_of_int n) term159 term81). Qed.
Lemma lem2594686 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2594687 : term81 = term161.
Proof. exact (@lem2594686 term82). Qed.
Lemma lem2594689 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2594690 : term159 = term164.
Proof. exact (@lem2594689 term82). Qed.
Lemma lem2594691 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2594692 : term165 = term166.
Proof. exact (MK_COMB (@lem2594691) (@lem2594690)). Qed.
Lemma lem2594693 : term167 = term168.
Proof. exact (MK_COMB (@lem2594692) (@lem2594687)). Qed.
Lemma lem2594694 : term168 = term169.
Proof. exact (@lem1981613 term159 term81 term81 term81). Qed.
Lemma lem2594696 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2594697 : term172 = term173.
Proof. exact (@lem2594696 term82 term82). Qed.
Lemma lem2594698 : (term174 = (BIT1 0)) = (term175 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2594699 : term175 = term82.
Proof. exact (EQ_MP (@lem2594698) (@lem940073)). Qed.
Lemma lem2594700 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2594701 : term173 = term81.
Proof. exact (MK_COMB (@lem2594700) (@lem2594699)). Qed.
Lemma lem2594702 : term172 = term81.
Proof. exact (TRANS (@lem2594697) (@lem2594701)). Qed.
Lemma lem2594704 (m : nat) (n : nat) : (term176 m n) = (term177 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2594705 : term167 = term178.
Proof. exact (@lem2594704 term82 term82). Qed.
Lemma lem2594706 : (term174 = (BIT1 0)) = (term175 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2594707 : term175 = term82.
Proof. exact (EQ_MP (@lem2594706) (@lem940073)). Qed.
Lemma lem2594708 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2594709 : term173 = term81.
Proof. exact (MK_COMB (@lem2594708) (@lem2594707)). Qed.
Lemma lem2594710 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2594711 : term178 = term159.
Proof. exact (MK_COMB (@lem2594710) (@lem2594709)). Qed.
Lemma lem2594712 : term167 = term159.
Proof. exact (TRANS (@lem2594705) (@lem2594711)). Qed.
Lemma lem2594713 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2594714 : term179 = term180.
Proof. exact (MK_COMB (@lem2594713) (@lem2594712)). Qed.
Lemma lem2594715 : term169 = term164.
Proof. exact (MK_COMB (@lem2594714) (@lem2594702)). Qed.
Lemma lem2594716 : term168 = term164.
Proof. exact (TRANS (@lem2594694) (@lem2594715)). Qed.
Lemma lem2594717 : term167 = term164.
Proof. exact (TRANS (@lem2594693) (@lem2594716)). Qed.
Lemma lem2594719 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2594720 : term164 = term159.
Proof. exact (@lem2594719 term159). Qed.
Lemma lem2594721 : term167 = term159.
Proof. exact (TRANS (@lem2594717) (@lem2594720)). Qed.
Lemma lem2594724 (n : int) : (term182 n) = (term182 n).
Proof. exact (eq_refl (term182 n)). Qed.
Lemma lem2594725 (n : int) : (term158 n) = (term183 n).
Proof. exact (MK_COMB (@lem2594724 n) (@lem2594721)). Qed.
Lemma lem2594726 (n : int) : (term157 n) = (term183 n).
Proof. exact (TRANS (@lem2594684 n) (@lem2594725 n)). Qed.
Lemma lem2594727 (n : int) : (term83 n) = (term83 n).
Proof. exact (eq_refl (term83 n)). Qed.
Lemma lem2594728 (n : int) : (term156 n) = (term184 n).
Proof. exact (MK_COMB (@lem2594727 n) (@lem2594726 n)). Qed.
Lemma lem2594729 (n : int) : (term184 n) = (term185 n).
Proof. exact (@lem1982763 (real_of_int n) (term186 n) term159). Qed.
Lemma lem2594730 (n : int) : (term187 n) = (term188 n).
Proof. exact (@lem1982715 term159 (real_of_int n)). Qed.
Lemma lem2594732 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2594733 : term81 = term161.
Proof. exact (@lem2594732 term82). Qed.
Lemma lem2594735 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2594736 : term159 = term164.
Proof. exact (@lem2594735 term82). Qed.
Lemma lem2594737 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2594738 : term189 = term190.
Proof. exact (MK_COMB (@lem2594737) (@lem2594736)). Qed.
Lemma lem2594739 : term191 = term192.
Proof. exact (MK_COMB (@lem2594738) (@lem2594733)). Qed.
Lemma lem2594740 : term193.
Proof. exact (@lem1981473 term159 term81 term81 term81 term99 term81). Qed.
Lemma lem2594742 (m : nat) (n : nat) : (term194 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2594743 : term195 = term196.
Proof. exact (@lem2594742 (NUMERAL 0) term82). Qed.
Lemma lem2594744 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2594745 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2594746 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2594745 h1) (fun h1 : term196 = True => @lem2594744)). Qed.
Lemma lem2594747 : term196 = True.
Proof. exact (EQ_MP (@lem2594746) (@lem2594744)). Qed.
Lemma lem2594748 : term195 = True.
Proof. exact (TRANS (@lem2594743) (@lem2594747)). Qed.
Lemma lem2594749 : True = term195.
Proof. exact (SYM (@lem2594748)). Qed.
Lemma lem2594750 : term195.
Proof. exact (EQ_MP (@lem2594749) (@lem0)). Qed.
Lemma lem2594751 : term198.
Proof. exact (@lem2594740 (@lem2594750)). Qed.
Lemma lem2594753 (m : nat) (n : nat) : (term194 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2594754 : term195 = term196.
Proof. exact (@lem2594753 (NUMERAL 0) term82). Qed.
Lemma lem2594755 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2594756 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2594757 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2594756 h1) (fun h1 : term196 = True => @lem2594755)). Qed.
Lemma lem2594758 : term196 = True.
Proof. exact (EQ_MP (@lem2594757) (@lem2594755)). Qed.
Lemma lem2594759 : term195 = True.
Proof. exact (TRANS (@lem2594754) (@lem2594758)). Qed.
Lemma lem2594760 : True = term195.
Proof. exact (SYM (@lem2594759)). Qed.
Lemma lem2594761 : term195.
Proof. exact (EQ_MP (@lem2594760) (@lem0)). Qed.
Lemma lem2594762 : term199.
Proof. exact (@lem2594751 (@lem2594761)). Qed.
Lemma lem2594764 (m : nat) (n : nat) : (term194 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2594765 : term195 = term196.
Proof. exact (@lem2594764 (NUMERAL 0) term82). Qed.
Lemma lem2594766 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2594767 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2594768 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2594767 h1) (fun h1 : term196 = True => @lem2594766)). Qed.
Lemma lem2594769 : term196 = True.
Proof. exact (EQ_MP (@lem2594768) (@lem2594766)). Qed.
Lemma lem2594770 : term195 = True.
Proof. exact (TRANS (@lem2594765) (@lem2594769)). Qed.
Lemma lem2594771 : True = term195.
Proof. exact (SYM (@lem2594770)). Qed.
Lemma lem2594772 : term195.
Proof. exact (EQ_MP (@lem2594771) (@lem0)). Qed.
Lemma lem2594773 : term200.
Proof. exact (@lem2594762 (@lem2594772)). Qed.
Lemma lem2594775 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2594776 : term172 = term173.
Proof. exact (@lem2594775 term82 term82). Qed.
Lemma lem2594777 : (term174 = (BIT1 0)) = (term175 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2594778 : term175 = term82.
Proof. exact (EQ_MP (@lem2594777) (@lem940073)). Qed.
Lemma lem2594779 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2594780 : term173 = term81.
Proof. exact (MK_COMB (@lem2594779) (@lem2594778)). Qed.
Lemma lem2594781 : term172 = term81.
Proof. exact (TRANS (@lem2594776) (@lem2594780)). Qed.
Lemma lem2594783 (m : nat) (n : nat) : (term176 m n) = (term177 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2594784 : term167 = term178.
Proof. exact (@lem2594783 term82 term82). Qed.
Lemma lem2594785 : (term174 = (BIT1 0)) = (term175 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2594786 : term175 = term82.
Proof. exact (EQ_MP (@lem2594785) (@lem940073)). Qed.
Lemma lem2594787 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2594788 : term173 = term81.
Proof. exact (MK_COMB (@lem2594787) (@lem2594786)). Qed.
Lemma lem2594789 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2594790 : term178 = term159.
Proof. exact (MK_COMB (@lem2594789) (@lem2594788)). Qed.
Lemma lem2594791 : term167 = term159.
Proof. exact (TRANS (@lem2594784) (@lem2594790)). Qed.
Lemma lem2594792 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2594793 : term201 = term189.
Proof. exact (MK_COMB (@lem2594792) (@lem2594791)). Qed.
Lemma lem2594794 : term202 = term191.
Proof. exact (MK_COMB (@lem2594793) (@lem2594781)). Qed.
Lemma lem2594796 (m : nat) : (term203 m) = term99.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2594797 : term191 = term99.
Proof. exact (@lem2594796 term82). Qed.
Lemma lem2594798 : term202 = term99.
Proof. exact (TRANS (@lem2594794) (@lem2594797)). Qed.
Lemma lem2594799 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2594800 : term204 = term205.
Proof. exact (MK_COMB (@lem2594799) (@lem2594798)). Qed.
Lemma lem2594801 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem2594802 : term206 = term207.
Proof. exact (MK_COMB (@lem2594800) (@lem2594801)). Qed.
Lemma lem2594804 (x : nat) : (term208 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2594805 : term207 = term99.
Proof. exact (@lem2594804 term82). Qed.
Lemma lem2594806 : term206 = term99.
Proof. exact (TRANS (@lem2594802) (@lem2594805)). Qed.
Lemma lem2594808 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2594809 : term172 = term173.
Proof. exact (@lem2594808 term82 term82). Qed.
Lemma lem2594810 : (term174 = (BIT1 0)) = (term175 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2594811 : term175 = term82.
Proof. exact (EQ_MP (@lem2594810) (@lem940073)). Qed.
Lemma lem2594812 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2594813 : term173 = term81.
Proof. exact (MK_COMB (@lem2594812) (@lem2594811)). Qed.
Lemma lem2594814 : term172 = term81.
Proof. exact (TRANS (@lem2594809) (@lem2594813)). Qed.
Lemma lem2594815 : term205 = term205.
Proof. exact (eq_refl term205). Qed.
Lemma lem2594816 : term209 = term207.
Proof. exact (MK_COMB (@lem2594815) (@lem2594814)). Qed.
Lemma lem2594818 (x : nat) : (term208 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2594819 : term207 = term99.
Proof. exact (@lem2594818 term82). Qed.
Lemma lem2594820 : term209 = term99.
Proof. exact (TRANS (@lem2594816) (@lem2594819)). Qed.
Lemma lem2594821 : term99 = term209.
Proof. exact (SYM (@lem2594820)). Qed.
Lemma lem2594822 : term206 = term209.
Proof. exact (TRANS (@lem2594806) (@lem2594821)). Qed.
Lemma lem2594823 : term192 = term210.
Proof. exact (@lem2594773 (@lem2594822)). Qed.
Lemma lem2594824 : term191 = term210.
Proof. exact (TRANS (@lem2594739) (@lem2594823)). Qed.
Lemma lem2594826 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2594827 : term210 = term99.
Proof. exact (@lem2594826 term99). Qed.
Lemma lem2594828 : term191 = term99.
Proof. exact (TRANS (@lem2594824) (@lem2594827)). Qed.
Lemma lem2594829 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2594830 : term211 = term205.
Proof. exact (MK_COMB (@lem2594829) (@lem2594828)). Qed.
Lemma lem2594831 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2594832 (n : int) : (term188 n) = (term212 n).
Proof. exact (MK_COMB (@lem2594830) (@lem2594831 n)). Qed.
Lemma lem2594833 (n : int) : (term187 n) = (term212 n).
Proof. exact (TRANS (@lem2594730 n) (@lem2594832 n)). Qed.
Lemma lem2594834 (n : int) : (term212 n) = term99.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2594835 (n : int) : (term187 n) = term99.
Proof. exact (TRANS (@lem2594833 n) (@lem2594834 n)). Qed.
Lemma lem2594836 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2594837 (n : int) : (term213 n) = term125.
Proof. exact (MK_COMB (@lem2594836) (@lem2594835 n)). Qed.
Lemma lem2594838 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2594839 (n : int) : (term185 n) = term214.
Proof. exact (MK_COMB (@lem2594837 n) (@lem2594838)). Qed.
Lemma lem2594840 (n : int) : (term184 n) = term214.
Proof. exact (TRANS (@lem2594729 n) (@lem2594839 n)). Qed.
Lemma lem2594841 : term214 = term159.
Proof. exact (@lem1982721 term159). Qed.
Lemma lem2594842 (n : int) : (term184 n) = term159.
Proof. exact (TRANS (@lem2594840 n) (@lem2594841)). Qed.
Lemma lem2594843 (n : int) : (term156 n) = term159.
Proof. exact (TRANS (@lem2594728 n) (@lem2594842 n)). Qed.
Lemma lem2594844 (n : int) : (term155 n) = term159.
Proof. exact (TRANS (@lem2594683 n) (@lem2594843 n)). Qed.
Lemma lem2594845 (n : int) : (term219 n) = term159.
Proof. exact (TRANS (@lem2594682 n) (@lem2594844 n)). Qed.
Lemma lem2594846 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2594847 (n : int) : (term220 n) = term216.
Proof. exact (MK_COMB (@lem2594846) (@lem2594845 n)). Qed.
Lemma lem2594848 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem2594849 (n : int) : (term218 n) = term217.
Proof. exact (MK_COMB (@lem2594847 n) (@lem2594848)). Qed.
Lemma lem2594850 (n : int) : (term114 n) = term217.
Proof. exact (TRANS (@lem2594659 n) (@lem2594849 n)). Qed.
Lemma lem2594851 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2594852 (n : int) : (term103 n) = term221.
Proof. exact (MK_COMB (@lem2594851) (@lem2594658 n)). Qed.
Lemma lem2594853 (n : int) : (term115 n) = term222.
Proof. exact (MK_COMB (@lem2594852 n) (@lem2594850 n)). Qed.
Lemma lem2594854 : term129 = term223.
Proof. exact (@lem1988287 term99 term126). Qed.
Lemma lem2594861 : term126 = term81.
Proof. exact (@lem1982721 term81). Qed.
Lemma lem2594864 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem2594865 : term225 = term226.
Proof. exact (MK_COMB (@lem2594864) (@lem2594861)). Qed.
Lemma lem2594866 : term226 = term227.
Proof. exact (@lem1982792 term99 term81). Qed.
Lemma lem2594868 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2594869 : term81 = term161.
Proof. exact (@lem2594868 term82). Qed.
Lemma lem2594871 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2594872 : term159 = term164.
Proof. exact (@lem2594871 term82). Qed.
Lemma lem2594873 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2594874 : term165 = term166.
Proof. exact (MK_COMB (@lem2594873) (@lem2594872)). Qed.
Lemma lem2594875 : term167 = term168.
Proof. exact (MK_COMB (@lem2594874) (@lem2594869)). Qed.
Lemma lem2594876 : term168 = term169.
Proof. exact (@lem1981613 term159 term81 term81 term81). Qed.
Lemma lem2594878 (m : nat) (n : nat) : (term170 m n) = (term171 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2594879 : term172 = term173.
Proof. exact (@lem2594878 term82 term82). Qed.
Lemma lem2594880 : (term174 = (BIT1 0)) = (term175 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2594881 : term175 = term82.
Proof. exact (EQ_MP (@lem2594880) (@lem940073)). Qed.
Lemma lem2594882 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2594883 : term173 = term81.
Proof. exact (MK_COMB (@lem2594882) (@lem2594881)). Qed.
Lemma lem2594884 : term172 = term81.
Proof. exact (TRANS (@lem2594879) (@lem2594883)). Qed.
Lemma lem2594886 (m : nat) (n : nat) : (term176 m n) = (term177 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2594887 : term167 = term178.
Proof. exact (@lem2594886 term82 term82). Qed.
Lemma lem2594888 : (term174 = (BIT1 0)) = (term175 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2594889 : term175 = term82.
Proof. exact (EQ_MP (@lem2594888) (@lem940073)). Qed.
Lemma lem2594890 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2594891 : term173 = term81.
Proof. exact (MK_COMB (@lem2594890) (@lem2594889)). Qed.
Lemma lem2594892 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2594893 : term178 = term159.
Proof. exact (MK_COMB (@lem2594892) (@lem2594891)). Qed.
Lemma lem2594894 : term167 = term159.
Proof. exact (TRANS (@lem2594887) (@lem2594893)). Qed.
Lemma lem2594895 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2594896 : term179 = term180.
Proof. exact (MK_COMB (@lem2594895) (@lem2594894)). Qed.
Lemma lem2594897 : term169 = term164.
Proof. exact (MK_COMB (@lem2594896) (@lem2594884)). Qed.
Lemma lem2594898 : term168 = term164.
Proof. exact (TRANS (@lem2594876) (@lem2594897)). Qed.
Lemma lem2594899 : term167 = term164.
Proof. exact (TRANS (@lem2594875) (@lem2594898)). Qed.
Lemma lem2594901 (x : real) : (term181 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2594902 : term164 = term159.
Proof. exact (@lem2594901 term159). Qed.
Lemma lem2594903 : term167 = term159.
Proof. exact (TRANS (@lem2594899) (@lem2594902)). Qed.
Lemma lem2594904 : term125 = term125.
Proof. exact (eq_refl term125). Qed.
Lemma lem2594905 : term227 = term214.
Proof. exact (MK_COMB (@lem2594904) (@lem2594903)). Qed.
Lemma lem2594906 : term214 = term159.
Proof. exact (@lem1982721 term159). Qed.
Lemma lem2594907 : term227 = term159.
Proof. exact (TRANS (@lem2594905) (@lem2594906)). Qed.
Lemma lem2594908 : term226 = term159.
Proof. exact (TRANS (@lem2594866) (@lem2594907)). Qed.
Lemma lem2594909 : term225 = term159.
Proof. exact (TRANS (@lem2594865) (@lem2594908)). Qed.
Lemma lem2594910 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2594911 : term228 = term216.
Proof. exact (MK_COMB (@lem2594910) (@lem2594909)). Qed.
Lemma lem2594912 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem2594913 : term223 = term217.
Proof. exact (MK_COMB (@lem2594911) (@lem2594912)). Qed.
Lemma lem2594914 : term129 = term217.
Proof. exact (TRANS (@lem2594854) (@lem2594913)). Qed.
Lemma lem2594915 : term142 = term229.
Proof. exact (@lem1988287 term99 term139). Qed.
Lemma lem2594923 : term230 = term231.
Proof. exact (@lem1982792 term99 term139). Qed.
Lemma lem2594928 : term231 = term232.
Proof. exact (@lem1982721 term232). Qed.
Lemma lem2594930 : term230 = term232.
Proof. exact (TRANS (@lem2594923) (@lem2594928)). Qed.
Lemma lem2594931 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2594932 : term233 = term234.
Proof. exact (MK_COMB (@lem2594931) (@lem2594930)). Qed.
Lemma lem2594933 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem2594934 : term229 = term235.
Proof. exact (MK_COMB (@lem2594932) (@lem2594933)). Qed.
Lemma lem2594935 : term142 = term235.
Proof. exact (TRANS (@lem2594915) (@lem2594934)). Qed.
Lemma lem2594936 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2594937 : term144 = term221.
Proof. exact (MK_COMB (@lem2594936) (@lem2594914)). Qed.
Lemma lem2594938 : term145 = term236.
Proof. exact (MK_COMB (@lem2594937) (@lem2594935)). Qed.
Lemma lem2594939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2594940 (n : int) : (term146 n) = term237.
Proof. exact (MK_COMB (@lem2594939) (@lem2594853 n)). Qed.
Lemma lem2594941 (n : int) : (term147 n) = term238.
Proof. exact (MK_COMB (@lem2594940 n) (@lem2594938)). Qed.
Lemma lem2594962 (n : int) : (term149 n) = term238.
Proof. exact (TRANS (@lem2594466 n) (@lem2594941 n)). Qed.
Lemma lem2594976 (x : real) (r : real) : (term239 x r) = (term240 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2594977 : term235 = term241.
Proof. exact (@lem2594976 term81 term99). Qed.
Lemma lem2594984 : term172 = term81.
Proof. exact (@lem1982733 term81). Qed.
Lemma lem2594985 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2594986 : term242 = term243.
Proof. exact (MK_COMB (@lem2594985) (@lem2594984)). Qed.
Lemma lem2594987 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem2594988 : term244 = term245.
Proof. exact (MK_COMB (@lem2594986) (@lem2594987)). Qed.
Lemma lem2594995 : term167 = term159.
Proof. exact (@lem1982735 term159). Qed.
Lemma lem2594996 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2594997 : term246 = term216.
Proof. exact (MK_COMB (@lem2594996) (@lem2594995)). Qed.
Lemma lem2594998 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem2594999 : term247 = term217.
Proof. exact (MK_COMB (@lem2594997) (@lem2594998)). Qed.
Lemma lem2595000 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2595001 : term248 = term249.
Proof. exact (MK_COMB (@lem2595000) (@lem2594999)). Qed.
Lemma lem2595002 : term241 = term250.
Proof. exact (MK_COMB (@lem2595001) (@lem2594988)). Qed.
Lemma lem2595005 : term235 = term250.
Proof. exact (TRANS (@lem2594977) (@lem2595002)). Qed.
Lemma lem2595007 : term221 = term221.
Proof. exact (eq_refl term221). Qed.
Lemma lem2595008 : term236 = term251.
Proof. exact (MK_COMB (@lem2595007) (@lem2595005)). Qed.
Lemma lem2595010 : term237 = term237.
Proof. exact (eq_refl term237). Qed.
Lemma lem2595011 : term238 = term252.
Proof. exact (MK_COMB (@lem2595010) (@lem2595008)). Qed.
Lemma lem2595012 (h1 : term252) : term252.
Proof. exact (h1). Qed.
Lemma lem2595013 (h1 : term222) : term222.
Proof. exact (h1). Qed.
Lemma lem2595014 (h1 : term217) : term217.
Proof. exact (h1). Qed.
Lemma lem2595016 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2595017 : term217 = term253.
Proof. exact (@lem2595016 term99 term159). Qed.
Lemma lem2595019 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2595020 : term159 = term164.
Proof. exact (@lem2595019 term82). Qed.
Lemma lem2595022 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2595023 : term99 = term210.
Proof. exact (@lem2595022 (NUMERAL 0)). Qed.
Lemma lem2595024 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2595025 : term254 = term255.
Proof. exact (MK_COMB (@lem2595024) (@lem2595023)). Qed.
Lemma lem2595026 : term253 = term256.
Proof. exact (MK_COMB (@lem2595025) (@lem2595020)). Qed.
Lemma lem2595027 : term257.
Proof. exact (@lem1980026 term99 term81 term159 term81). Qed.
Lemma lem2595029 (m : nat) (n : nat) : (term194 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2595030 : term195 = term196.
Proof. exact (@lem2595029 (NUMERAL 0) term82). Qed.
Lemma lem2595031 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2595032 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2595033 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2595032 h1) (fun h1 : term196 = True => @lem2595031)). Qed.
Lemma lem2595034 : term196 = True.
Proof. exact (EQ_MP (@lem2595033) (@lem2595031)). Qed.
Lemma lem2595035 : term195 = True.
Proof. exact (TRANS (@lem2595030) (@lem2595034)). Qed.
Lemma lem2595036 : True = term195.
Proof. exact (SYM (@lem2595035)). Qed.
Lemma lem2595037 : term195.
Proof. exact (EQ_MP (@lem2595036) (@lem0)). Qed.
Lemma lem2595038 : term258.
Proof. exact (@lem2595027 (@lem2595037)). Qed.
Lemma lem2595040 (m : nat) (n : nat) : (term194 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2595041 : term195 = term196.
Proof. exact (@lem2595040 (NUMERAL 0) term82). Qed.
Lemma lem2595042 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2595043 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2595044 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2595043 h1) (fun h1 : term196 = True => @lem2595042)). Qed.
Lemma lem2595045 : term196 = True.
Proof. exact (EQ_MP (@lem2595044) (@lem2595042)). Qed.
Lemma lem2595046 : term195 = True.
Proof. exact (TRANS (@lem2595041) (@lem2595045)). Qed.
Lemma lem2595047 : True = term195.
Proof. exact (SYM (@lem2595046)). Qed.
Lemma lem2595048 : term195.
Proof. exact (EQ_MP (@lem2595047) (@lem0)). Qed.
Lemma lem2595049 : term256 = term259.
Proof. exact (@lem2595038 (@lem2595048)). Qed.
Lemma lem2595051 (m : nat) (n : nat) : (term176 m n) = (term177 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2595052 : term167 = term178.
Proof. exact (@lem2595051 term82 term82). Qed.
Lemma lem2595053 : (term174 = (BIT1 0)) = (term175 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2595054 : term175 = term82.
Proof. exact (EQ_MP (@lem2595053) (@lem940073)). Qed.
Lemma lem2595055 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2595056 : term173 = term81.
Proof. exact (MK_COMB (@lem2595055) (@lem2595054)). Qed.
Lemma lem2595057 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2595058 : term178 = term159.
Proof. exact (MK_COMB (@lem2595057) (@lem2595056)). Qed.
Lemma lem2595059 : term167 = term159.
Proof. exact (TRANS (@lem2595052) (@lem2595058)). Qed.
Lemma lem2595061 (x : nat) : (term208 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2595062 : term207 = term99.
Proof. exact (@lem2595061 term82). Qed.
Lemma lem2595063 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2595064 : term260 = term254.
Proof. exact (MK_COMB (@lem2595063) (@lem2595062)). Qed.
Lemma lem2595065 : term259 = term253.
Proof. exact (MK_COMB (@lem2595064) (@lem2595059)). Qed.
Lemma lem2595067 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2595068 : term253 = term263.
Proof. exact (@lem2595067 (NUMERAL 0) term82). Qed.
Lemma lem2595069 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2595070 (h1 : term197 = (BIT1 0)) : (term82 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2595071 : (term197 = (BIT1 0)) = ((term82 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2595070 h1) (fun h1 : (term82 = (NUMERAL 0)) = False => @lem2595069)). Qed.
Lemma lem2595072 : (term82 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2595071) (@lem2595069)). Qed.
Lemma lem2595073 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2595074 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2595075 : term264 = (and True).
Proof. exact (MK_COMB (@lem2595074) (@lem2595073)). Qed.
Lemma lem2595076 : term263 = (True /\ False).
Proof. exact (MK_COMB (@lem2595075) (@lem2595072)). Qed.
Lemma lem2595078 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2595079 : term263 = False.
Proof. exact (TRANS (@lem2595076) (@lem2595078)). Qed.
Lemma lem2595080 : term253 = False.
Proof. exact (TRANS (@lem2595068) (@lem2595079)). Qed.
Lemma lem2595081 : term259 = False.
Proof. exact (TRANS (@lem2595065) (@lem2595080)). Qed.
Lemma lem2595082 : term256 = False.
Proof. exact (TRANS (@lem2595049) (@lem2595081)). Qed.
Lemma lem2595083 : term253 = False.
Proof. exact (TRANS (@lem2595026) (@lem2595082)). Qed.
Lemma lem2595084 : term217 = False.
Proof. exact (TRANS (@lem2595017) (@lem2595083)). Qed.
Lemma lem2595085 (h1 : term217) : False.
Proof. exact (EQ_MP (@lem2595084) (@lem2595014 h1)). Qed.
Lemma lem2595086 (h1 : term217) : term217.
Proof. exact (h1). Qed.
Lemma lem2595088 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2595089 : term217 = term253.
Proof. exact (@lem2595088 term99 term159). Qed.
Lemma lem2595091 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2595092 : term159 = term164.
Proof. exact (@lem2595091 term82). Qed.
Lemma lem2595094 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2595095 : term99 = term210.
Proof. exact (@lem2595094 (NUMERAL 0)). Qed.
Lemma lem2595096 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2595097 : term254 = term255.
Proof. exact (MK_COMB (@lem2595096) (@lem2595095)). Qed.
Lemma lem2595098 : term253 = term256.
Proof. exact (MK_COMB (@lem2595097) (@lem2595092)). Qed.
Lemma lem2595099 : term257.
Proof. exact (@lem1980026 term99 term81 term159 term81). Qed.
Lemma lem2595101 (m : nat) (n : nat) : (term194 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2595102 : term195 = term196.
Proof. exact (@lem2595101 (NUMERAL 0) term82). Qed.
Lemma lem2595103 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2595104 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2595105 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2595104 h1) (fun h1 : term196 = True => @lem2595103)). Qed.
Lemma lem2595106 : term196 = True.
Proof. exact (EQ_MP (@lem2595105) (@lem2595103)). Qed.
Lemma lem2595107 : term195 = True.
Proof. exact (TRANS (@lem2595102) (@lem2595106)). Qed.
Lemma lem2595108 : True = term195.
Proof. exact (SYM (@lem2595107)). Qed.
Lemma lem2595109 : term195.
Proof. exact (EQ_MP (@lem2595108) (@lem0)). Qed.
Lemma lem2595110 : term258.
Proof. exact (@lem2595099 (@lem2595109)). Qed.
Lemma lem2595112 (m : nat) (n : nat) : (term194 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2595113 : term195 = term196.
Proof. exact (@lem2595112 (NUMERAL 0) term82). Qed.
Lemma lem2595114 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2595115 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2595116 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2595115 h1) (fun h1 : term196 = True => @lem2595114)). Qed.
Lemma lem2595117 : term196 = True.
Proof. exact (EQ_MP (@lem2595116) (@lem2595114)). Qed.
Lemma lem2595118 : term195 = True.
Proof. exact (TRANS (@lem2595113) (@lem2595117)). Qed.
Lemma lem2595119 : True = term195.
Proof. exact (SYM (@lem2595118)). Qed.
Lemma lem2595120 : term195.
Proof. exact (EQ_MP (@lem2595119) (@lem0)). Qed.
Lemma lem2595121 : term256 = term259.
Proof. exact (@lem2595110 (@lem2595120)). Qed.
Lemma lem2595123 (m : nat) (n : nat) : (term176 m n) = (term177 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2595124 : term167 = term178.
Proof. exact (@lem2595123 term82 term82). Qed.
Lemma lem2595125 : (term174 = (BIT1 0)) = (term175 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2595126 : term175 = term82.
Proof. exact (EQ_MP (@lem2595125) (@lem940073)). Qed.
Lemma lem2595127 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2595128 : term173 = term81.
Proof. exact (MK_COMB (@lem2595127) (@lem2595126)). Qed.
Lemma lem2595129 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2595130 : term178 = term159.
Proof. exact (MK_COMB (@lem2595129) (@lem2595128)). Qed.
Lemma lem2595131 : term167 = term159.
Proof. exact (TRANS (@lem2595124) (@lem2595130)). Qed.
Lemma lem2595133 (x : nat) : (term208 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2595134 : term207 = term99.
Proof. exact (@lem2595133 term82). Qed.
Lemma lem2595135 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2595136 : term260 = term254.
Proof. exact (MK_COMB (@lem2595135) (@lem2595134)). Qed.
Lemma lem2595137 : term259 = term253.
Proof. exact (MK_COMB (@lem2595136) (@lem2595131)). Qed.
Lemma lem2595139 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2595140 : term253 = term263.
Proof. exact (@lem2595139 (NUMERAL 0) term82). Qed.
Lemma lem2595141 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2595142 (h1 : term197 = (BIT1 0)) : (term82 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2595143 : (term197 = (BIT1 0)) = ((term82 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2595142 h1) (fun h1 : (term82 = (NUMERAL 0)) = False => @lem2595141)). Qed.
Lemma lem2595144 : (term82 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2595143) (@lem2595141)). Qed.
Lemma lem2595145 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2595146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2595147 : term264 = (and True).
Proof. exact (MK_COMB (@lem2595146) (@lem2595145)). Qed.
Lemma lem2595148 : term263 = (True /\ False).
Proof. exact (MK_COMB (@lem2595147) (@lem2595144)). Qed.
Lemma lem2595150 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2595151 : term263 = False.
Proof. exact (TRANS (@lem2595148) (@lem2595150)). Qed.
Lemma lem2595152 : term253 = False.
Proof. exact (TRANS (@lem2595140) (@lem2595151)). Qed.
Lemma lem2595153 : term259 = False.
Proof. exact (TRANS (@lem2595137) (@lem2595152)). Qed.
Lemma lem2595154 : term256 = False.
Proof. exact (TRANS (@lem2595121) (@lem2595153)). Qed.
Lemma lem2595155 : term253 = False.
Proof. exact (TRANS (@lem2595098) (@lem2595154)). Qed.
Lemma lem2595156 : term217 = False.
Proof. exact (TRANS (@lem2595089) (@lem2595155)). Qed.
Lemma lem2595157 (h1 : term217) : False.
Proof. exact (EQ_MP (@lem2595156) (@lem2595086 h1)). Qed.
Lemma lem2595158 (h1 : term222) : False.
Proof. exact (or_elim (@lem2595013 h1) (fun h0 : term217 => @lem2595085 h0) (fun h0 : term217 => @lem2595157 h0)). Qed.
Lemma lem2595159 (h1 : term251) : term251.
Proof. exact (h1). Qed.
Lemma lem2595160 (h1 : term217) : term217.
Proof. exact (h1). Qed.
Lemma lem2595162 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2595163 : term217 = term253.
Proof. exact (@lem2595162 term99 term159). Qed.
Lemma lem2595165 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2595166 : term159 = term164.
Proof. exact (@lem2595165 term82). Qed.
Lemma lem2595168 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2595169 : term99 = term210.
Proof. exact (@lem2595168 (NUMERAL 0)). Qed.
Lemma lem2595170 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2595171 : term254 = term255.
Proof. exact (MK_COMB (@lem2595170) (@lem2595169)). Qed.
Lemma lem2595172 : term253 = term256.
Proof. exact (MK_COMB (@lem2595171) (@lem2595166)). Qed.
Lemma lem2595173 : term257.
Proof. exact (@lem1980026 term99 term81 term159 term81). Qed.
Lemma lem2595175 (m : nat) (n : nat) : (term194 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2595176 : term195 = term196.
Proof. exact (@lem2595175 (NUMERAL 0) term82). Qed.
Lemma lem2595177 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2595178 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2595179 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2595178 h1) (fun h1 : term196 = True => @lem2595177)). Qed.
Lemma lem2595180 : term196 = True.
Proof. exact (EQ_MP (@lem2595179) (@lem2595177)). Qed.
Lemma lem2595181 : term195 = True.
Proof. exact (TRANS (@lem2595176) (@lem2595180)). Qed.
Lemma lem2595182 : True = term195.
Proof. exact (SYM (@lem2595181)). Qed.
Lemma lem2595183 : term195.
Proof. exact (EQ_MP (@lem2595182) (@lem0)). Qed.
Lemma lem2595184 : term258.
Proof. exact (@lem2595173 (@lem2595183)). Qed.
Lemma lem2595186 (m : nat) (n : nat) : (term194 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2595187 : term195 = term196.
Proof. exact (@lem2595186 (NUMERAL 0) term82). Qed.
Lemma lem2595188 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2595189 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2595190 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2595189 h1) (fun h1 : term196 = True => @lem2595188)). Qed.
Lemma lem2595191 : term196 = True.
Proof. exact (EQ_MP (@lem2595190) (@lem2595188)). Qed.
Lemma lem2595192 : term195 = True.
Proof. exact (TRANS (@lem2595187) (@lem2595191)). Qed.
Lemma lem2595193 : True = term195.
Proof. exact (SYM (@lem2595192)). Qed.
Lemma lem2595194 : term195.
Proof. exact (EQ_MP (@lem2595193) (@lem0)). Qed.
Lemma lem2595195 : term256 = term259.
Proof. exact (@lem2595184 (@lem2595194)). Qed.
Lemma lem2595197 (m : nat) (n : nat) : (term176 m n) = (term177 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2595198 : term167 = term178.
Proof. exact (@lem2595197 term82 term82). Qed.
Lemma lem2595199 : (term174 = (BIT1 0)) = (term175 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2595200 : term175 = term82.
Proof. exact (EQ_MP (@lem2595199) (@lem940073)). Qed.
Lemma lem2595201 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2595202 : term173 = term81.
Proof. exact (MK_COMB (@lem2595201) (@lem2595200)). Qed.
Lemma lem2595203 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2595204 : term178 = term159.
Proof. exact (MK_COMB (@lem2595203) (@lem2595202)). Qed.
Lemma lem2595205 : term167 = term159.
Proof. exact (TRANS (@lem2595198) (@lem2595204)). Qed.
Lemma lem2595207 (x : nat) : (term208 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2595208 : term207 = term99.
Proof. exact (@lem2595207 term82). Qed.
Lemma lem2595209 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2595210 : term260 = term254.
Proof. exact (MK_COMB (@lem2595209) (@lem2595208)). Qed.
Lemma lem2595211 : term259 = term253.
Proof. exact (MK_COMB (@lem2595210) (@lem2595205)). Qed.
Lemma lem2595213 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2595214 : term253 = term263.
Proof. exact (@lem2595213 (NUMERAL 0) term82). Qed.
Lemma lem2595215 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2595216 (h1 : term197 = (BIT1 0)) : (term82 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2595217 : (term197 = (BIT1 0)) = ((term82 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2595216 h1) (fun h1 : (term82 = (NUMERAL 0)) = False => @lem2595215)). Qed.
Lemma lem2595218 : (term82 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2595217) (@lem2595215)). Qed.
Lemma lem2595219 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2595220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2595221 : term264 = (and True).
Proof. exact (MK_COMB (@lem2595220) (@lem2595219)). Qed.
Lemma lem2595222 : term263 = (True /\ False).
Proof. exact (MK_COMB (@lem2595221) (@lem2595218)). Qed.
Lemma lem2595224 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2595225 : term263 = False.
Proof. exact (TRANS (@lem2595222) (@lem2595224)). Qed.
Lemma lem2595226 : term253 = False.
Proof. exact (TRANS (@lem2595214) (@lem2595225)). Qed.
Lemma lem2595227 : term259 = False.
Proof. exact (TRANS (@lem2595211) (@lem2595226)). Qed.
Lemma lem2595228 : term256 = False.
Proof. exact (TRANS (@lem2595195) (@lem2595227)). Qed.
Lemma lem2595229 : term253 = False.
Proof. exact (TRANS (@lem2595172) (@lem2595228)). Qed.
Lemma lem2595230 : term217 = False.
Proof. exact (TRANS (@lem2595163) (@lem2595229)). Qed.
Lemma lem2595231 (h1 : term217) : False.
Proof. exact (EQ_MP (@lem2595230) (@lem2595160 h1)). Qed.
Lemma lem2595232 (h1 : term250) : term250.
Proof. exact (h1). Qed.
Lemma lem2595234 (h1 : term250) : term217.
Proof. exact (proj1 (@lem2595232 h1)). Qed.
Lemma lem2595236 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2595237 : term217 = term253.
Proof. exact (@lem2595236 term99 term159). Qed.
Lemma lem2595239 (x : nat) : (term162 x) = (term163 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2595240 : term159 = term164.
Proof. exact (@lem2595239 term82). Qed.
Lemma lem2595242 (x : nat) : (real_of_num x) = (term160 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2595243 : term99 = term210.
Proof. exact (@lem2595242 (NUMERAL 0)). Qed.
Lemma lem2595244 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2595245 : term254 = term255.
Proof. exact (MK_COMB (@lem2595244) (@lem2595243)). Qed.
Lemma lem2595246 : term253 = term256.
Proof. exact (MK_COMB (@lem2595245) (@lem2595240)). Qed.
Lemma lem2595247 : term257.
Proof. exact (@lem1980026 term99 term81 term159 term81). Qed.
Lemma lem2595249 (m : nat) (n : nat) : (term194 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2595250 : term195 = term196.
Proof. exact (@lem2595249 (NUMERAL 0) term82). Qed.
Lemma lem2595251 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2595252 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2595253 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2595252 h1) (fun h1 : term196 = True => @lem2595251)). Qed.
Lemma lem2595254 : term196 = True.
Proof. exact (EQ_MP (@lem2595253) (@lem2595251)). Qed.
Lemma lem2595255 : term195 = True.
Proof. exact (TRANS (@lem2595250) (@lem2595254)). Qed.
Lemma lem2595256 : True = term195.
Proof. exact (SYM (@lem2595255)). Qed.
Lemma lem2595257 : term195.
Proof. exact (EQ_MP (@lem2595256) (@lem0)). Qed.
Lemma lem2595258 : term258.
Proof. exact (@lem2595247 (@lem2595257)). Qed.
Lemma lem2595260 (m : nat) (n : nat) : (term194 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2595261 : term195 = term196.
Proof. exact (@lem2595260 (NUMERAL 0) term82). Qed.
Lemma lem2595262 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2595263 (h1 : term197 = (BIT1 0)) : term196 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2595264 : (term197 = (BIT1 0)) = (term196 = True).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2595263 h1) (fun h1 : term196 = True => @lem2595262)). Qed.
Lemma lem2595265 : term196 = True.
Proof. exact (EQ_MP (@lem2595264) (@lem2595262)). Qed.
Lemma lem2595266 : term195 = True.
Proof. exact (TRANS (@lem2595261) (@lem2595265)). Qed.
Lemma lem2595267 : True = term195.
Proof. exact (SYM (@lem2595266)). Qed.
Lemma lem2595268 : term195.
Proof. exact (EQ_MP (@lem2595267) (@lem0)). Qed.
Lemma lem2595269 : term256 = term259.
Proof. exact (@lem2595258 (@lem2595268)). Qed.
Lemma lem2595271 (m : nat) (n : nat) : (term176 m n) = (term177 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2595272 : term167 = term178.
Proof. exact (@lem2595271 term82 term82). Qed.
Lemma lem2595273 : (term174 = (BIT1 0)) = (term175 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2595274 : term175 = term82.
Proof. exact (EQ_MP (@lem2595273) (@lem940073)). Qed.
Lemma lem2595275 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2595276 : term173 = term81.
Proof. exact (MK_COMB (@lem2595275) (@lem2595274)). Qed.
Lemma lem2595277 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2595278 : term178 = term159.
Proof. exact (MK_COMB (@lem2595277) (@lem2595276)). Qed.
Lemma lem2595279 : term167 = term159.
Proof. exact (TRANS (@lem2595272) (@lem2595278)). Qed.
Lemma lem2595281 (x : nat) : (term208 x) = term99.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2595282 : term207 = term99.
Proof. exact (@lem2595281 term82). Qed.
Lemma lem2595283 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2595284 : term260 = term254.
Proof. exact (MK_COMB (@lem2595283) (@lem2595282)). Qed.
Lemma lem2595285 : term259 = term253.
Proof. exact (MK_COMB (@lem2595284) (@lem2595279)). Qed.
Lemma lem2595287 (m : nat) (n : nat) : (term261 m n) = (term262 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2595288 : term253 = term263.
Proof. exact (@lem2595287 (NUMERAL 0) term82). Qed.
Lemma lem2595289 : term197 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2595290 (h1 : term197 = (BIT1 0)) : (term82 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2595291 : (term197 = (BIT1 0)) = ((term82 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term197 = (BIT1 0) => @lem2595290 h1) (fun h1 : (term82 = (NUMERAL 0)) = False => @lem2595289)). Qed.
Lemma lem2595292 : (term82 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2595291) (@lem2595289)). Qed.
Lemma lem2595293 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2595294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2595295 : term264 = (and True).
Proof. exact (MK_COMB (@lem2595294) (@lem2595293)). Qed.
Lemma lem2595296 : term263 = (True /\ False).
Proof. exact (MK_COMB (@lem2595295) (@lem2595292)). Qed.
Lemma lem2595298 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2595299 : term263 = False.
Proof. exact (TRANS (@lem2595296) (@lem2595298)). Qed.
Lemma lem2595300 : term253 = False.
Proof. exact (TRANS (@lem2595288) (@lem2595299)). Qed.
Lemma lem2595301 : term259 = False.
Proof. exact (TRANS (@lem2595285) (@lem2595300)). Qed.
Lemma lem2595302 : term256 = False.
Proof. exact (TRANS (@lem2595269) (@lem2595301)). Qed.
Lemma lem2595303 : term253 = False.
Proof. exact (TRANS (@lem2595246) (@lem2595302)). Qed.
Lemma lem2595304 : term217 = False.
Proof. exact (TRANS (@lem2595237) (@lem2595303)). Qed.
Lemma lem2595305 (h1 : term250) : False.
Proof. exact (EQ_MP (@lem2595304) (@lem2595234 h1)). Qed.
Lemma lem2595306 (h1 : term251) : False.
Proof. exact (or_elim (@lem2595159 h1) (fun h0 : term217 => @lem2595231 h0) (fun h0 : term250 => @lem2595305 h0)). Qed.
Lemma lem2595307 (h1 : term252) : False.
Proof. exact (or_elim (@lem2595012 h1) (fun h0 : term222 => @lem2595158 h0) (fun h0 : term251 => @lem2595306 h0)). Qed.
Lemma lem2595308 (h1 : term238) : term238.
Proof. exact (h1). Qed.
Lemma lem2595309 (h1 : term238) : term252.
Proof. exact (EQ_MP (@lem2595011) (@lem2595308 h1)). Qed.
Lemma lem2595310 (h1 : term238) : term252 = False.
Proof. exact (prop_ext (fun h2 : term252 => @lem2595307 h2) (fun h2 : False => @lem2595309 h1)). Qed.
Lemma lem2595311 (h1 : term238) : False.
Proof. exact (EQ_MP (@lem2595310 h1) (@lem2595309 h1)). Qed.
Lemma lem2595312 (n : int) (h1 : term149 n) : term149 n.
Proof. exact (h1). Qed.
Lemma lem2595313 (n : int) (h1 : term149 n) : term238.
Proof. exact (EQ_MP (@lem2594962 n) (@lem2595312 n h1)). Qed.
Lemma lem2595314 (n : int) (h1 : term149 n) : term238 = False.
Proof. exact (prop_ext (fun h2 : term238 => @lem2595311 h2) (fun h2 : False => @lem2595313 n h1)). Qed.
Lemma lem2595315 (n : int) (h1 : term149 n) : False.
Proof. exact (EQ_MP (@lem2595314 n h1) (@lem2595313 n h1)). Qed.
Lemma lem2595316 (n : int) : term265 n.
Proof. exact (fun h0 : term149 n => @lem2595315 n h0). Qed.
Lemma lem2595317 (n : int) : term266 n.
Proof. exact (@lem1386578 (term267 n)). Qed.
Lemma lem2595320 (n : int) : term267 n.
Proof. exact (@lem2595317 n (@lem2595316 n)). Qed.
Lemma lem2595321 (n : int) : (term147 n) = (term64 n).
Proof. exact (SYM (@lem2594426 n)). Qed.
Lemma lem2595322 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2595323 (n : int) : (term267 n) = (term55 n).
Proof. exact (MK_COMB (@lem2595322) (@lem2595321 n)). Qed.
Lemma lem2595324 (n : int) : term55 n.
Proof. exact (EQ_MP (@lem2595323 n) (@lem2595320 n)). Qed.
Lemma lem2595325 (n : int) : term56 n.
Proof. exact (EQ_MP (@lem2594251 n) (@lem2595324 n)). Qed.
Lemma lem2595326 (n : int) : (term56 n) = ((term56 n) = True).
Proof. exact (@lem7 (term56 n)). Qed.
Lemma lem2595327 (n : int) : (term56 n) = True.
Proof. exact (EQ_MP (@lem2595326 n) (@lem2595325 n)). Qed.
Lemma lem2595328 (n : int) : True = (term56 n).
Proof. exact (SYM (@lem2595327 n)). Qed.
Lemma lem2595329 (n : int) : term56 n.
Proof. exact (EQ_MP (@lem2595328 n) (@lem0)). Qed.
Lemma lem2595330 (n : int) : term49 n.
Proof. exact (@lem2594250 n (@lem2595329 n)). Qed.
Lemma lem2595335 : term52.
Proof. exact (fun n : int => @lem2595330 n). Qed.
Lemma lem2595336 : term43.
Proof. exact (EQ_MP (@lem2594247) (@lem2595335)). Qed.
