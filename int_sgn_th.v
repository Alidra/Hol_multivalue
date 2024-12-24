Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_sgn_th_term_abbrevs.
Require Import int_sgn_spec.
Require Import is_int_spec.
Require Import real_sgn_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16451_spec.
Require Import thm16452_spec.
Require Import thm16474_spec.
Require Import thm17160_spec.
Require Import thm17784_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm2267742_spec.
Require Import thm69_spec.
Lemma lem2288999 : term0.
Proof. exact (fun x : real => @lem2267614 x). Qed.
Lemma lem2289000 (r : real) (h1 : (integer r) = ((term1 r) = r)) : (integer r) = ((term1 r) = r).
Proof. exact (h1). Qed.
Lemma lem2289001 (r : real) (h1 : (integer r) = ((term1 r) = r)) : ((term1 r) = r) = (integer r).
Proof. exact (SYM (@lem2289000 r h1)). Qed.
Lemma lem2289002 (r : real) (h1 : ((term1 r) = r) = (integer r)) : ((term1 r) = r) = (integer r).
Proof. exact (h1). Qed.
Lemma lem2289003 (r : real) (h1 : ((term1 r) = r) = (integer r)) : (integer r) = ((term1 r) = r).
Proof. exact (SYM (@lem2289002 r h1)). Qed.
Lemma lem2289004 (r : real) : ((integer r) = ((term1 r) = r)) = (((term1 r) = r) = (integer r)).
Proof. exact (prop_ext (fun h1 : (integer r) = ((term1 r) = r) => @lem2289001 r h1) (fun h1 : ((term1 r) = r) = (integer r) => @lem2289003 r h1)). Qed.
Lemma lem2289006 (x : real) : term2 x.
Proof. exact (@lem1710164 x). Qed.
Lemma lem2289007 (x : real) : (term2 x) = ((real_sgn x) = (term3 x)).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem2289009 (x : int) : term4 x.
Proof. exact (@lem2288988 x). Qed.
Lemma lem2289010 (x : int) : (term4 x) = ((int_sgn x) = (term5 x)).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem2289015 (x : int) : (int_sgn x) = (term5 x).
Proof. exact (EQ_MP (@lem2289010 x) (@lem2289009 x)). Qed.
Lemma lem2289017 (x : real) : (real_sgn x) = (term3 x).
Proof. exact (EQ_MP (@lem2289007 x) (@lem2289006 x)). Qed.
Lemma lem2289018 (x : int) : (term6 x) = (term7 x).
Proof. exact (@lem2289017 (real_of_int x)). Qed.
Lemma lem2289019 : int_of_real = int_of_real.
Proof. exact (eq_refl int_of_real). Qed.
Lemma lem2289020 (x : int) : (term5 x) = (term8 x).
Proof. exact (MK_COMB (@lem2289019) (@lem2289018 x)). Qed.
Lemma lem2289021 (x : int) : (int_sgn x) = (term8 x).
Proof. exact (TRANS (@lem2289015 x) (@lem2289020 x)). Qed.
Lemma lem2289022 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2289023 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2289022) (@lem2289021 x)). Qed.
Lemma lem2289024 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2289025 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2289024) (@lem2289023 x)). Qed.
Lemma lem2289027 (x : real) : (real_sgn x) = (term3 x).
Proof. exact (EQ_MP (@lem2289007 x) (@lem2289006 x)). Qed.
Lemma lem2289028 (x : int) : (term6 x) = (term7 x).
Proof. exact (@lem2289027 (real_of_int x)). Qed.
Lemma lem2289029 (x : int) : ((term9 x) = (term6 x)) = ((term10 x) = (term7 x)).
Proof. exact (MK_COMB (@lem2289025 x) (@lem2289028 x)). Qed.
Lemma lem2289031 (r : real) : ((term1 r) = r) = (integer r).
Proof. exact (EQ_MP (@lem2289004 r) (@lem2267742 r)). Qed.
Lemma lem2289032 (x : int) : ((term10 x) = (term7 x)) = (term13 x).
Proof. exact (@lem2289031 (term7 x)). Qed.
Lemma lem2289033 (x : int) : ((term9 x) = (term6 x)) = (term13 x).
Proof. exact (TRANS (@lem2289029 x) (@lem2289032 x)). Qed.
Lemma lem2289034 (x : int) : (term13 x) = ((term9 x) = (term6 x)).
Proof. exact (SYM (@lem2289033 x)). Qed.
Lemma lem2289035 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term14 _476 _475 _474 _477) = (term15 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem2289036 (_474 : real) (_475 : Prop) (_477 : real) : (term16 _475 _474 _477) = (term17 _474 _475 _477).
Proof. exact (@lem2289035 _474 _475 term18 _477). Qed.
Lemma lem2289037 (x : int) : (term19 x) = (term20 x).
Proof. exact (@lem2289036 term21 (term22 x) (term23 x)). Qed.
Lemma lem2289038 (x : int) : (term24 x) = (term25 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem2289039 (x : int) : (term26 x) = (term26 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem2289040 (x : int) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem2289039 x) (@lem2289038 x)). Qed.
Lemma lem2289041 : term29 = term30.
Proof. exact (eq_refl term29). Qed.
Lemma lem2289042 (x : int) : (term31 x) = (term31 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem2289043 (x : int) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem2289042 x) (@lem2289041)). Qed.
Lemma lem2289044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2289045 (x : int) : (term34 x) = (term35 x).
Proof. exact (MK_COMB (@lem2289044) (@lem2289043 x)). Qed.
Lemma lem2289046 (x : int) : (term20 x) = (term36 x).
Proof. exact (MK_COMB (@lem2289045 x) (@lem2289040 x)). Qed.
Lemma lem2289047 (x : int) : (term19 x) = (term13 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem2289048 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2289049 (x : int) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem2289048) (@lem2289047 x)). Qed.
Lemma lem2289050 (x : int) : ((term19 x) = (term20 x)) = ((term13 x) = (term36 x)).
Proof. exact (MK_COMB (@lem2289049 x) (@lem2289046 x)). Qed.
Lemma lem2289051 (x : int) : (term13 x) = (term36 x).
Proof. exact (EQ_MP (@lem2289050 x) (@lem2289037 x)). Qed.
Lemma lem2289052 (x : int) : (term36 x) = (term13 x).
Proof. exact (SYM (@lem2289051 x)). Qed.
Lemma lem2289095 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term14 _476 _475 _474 _477) = (term15 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem2289096 (_474 : real) (_475 : Prop) (_477 : real) : (term16 _475 _474 _477) = (term17 _474 _475 _477).
Proof. exact (@lem2289095 _474 _475 term18 _477). Qed.
Lemma lem2289097 (x : int) : (term24 x) = (term39 x).
Proof. exact (@lem2289096 term40 (term41 x) term42). Qed.
Lemma lem2289098 : term43 = term44.
Proof. exact (eq_refl term43). Qed.
Lemma lem2289099 (x : int) : (term45 x) = (term45 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem2289100 (x : int) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem2289099 x) (@lem2289098)). Qed.
Lemma lem2289101 : term48 = term49.
Proof. exact (eq_refl term48). Qed.
Lemma lem2289102 (x : int) : (term50 x) = (term50 x).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem2289103 (x : int) : (term51 x) = (term52 x).
Proof. exact (MK_COMB (@lem2289102 x) (@lem2289101)). Qed.
Lemma lem2289104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2289105 (x : int) : (term53 x) = (term54 x).
Proof. exact (MK_COMB (@lem2289104) (@lem2289103 x)). Qed.
Lemma lem2289106 (x : int) : (term39 x) = (term55 x).
Proof. exact (MK_COMB (@lem2289105 x) (@lem2289100 x)). Qed.
Lemma lem2289107 (x : int) : (term24 x) = (term25 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem2289108 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2289109 (x : int) : (term56 x) = (term57 x).
Proof. exact (MK_COMB (@lem2289108) (@lem2289107 x)). Qed.
Lemma lem2289110 (x : int) : ((term24 x) = (term39 x)) = ((term25 x) = (term55 x)).
Proof. exact (MK_COMB (@lem2289109 x) (@lem2289106 x)). Qed.
Lemma lem2289111 (x : int) : (term25 x) = (term55 x).
Proof. exact (EQ_MP (@lem2289110 x) (@lem2289097 x)). Qed.
Lemma lem2289112 (x : int) : (term55 x) = (term25 x).
Proof. exact (SYM (@lem2289111 x)). Qed.
Lemma lem2289160 (p : Prop) : p = (term58 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2289161 : term30 = term59.
Proof. exact (@lem2289160 term30). Qed.
Lemma lem2289162 : term59 = term30.
Proof. exact (SYM (@lem2289161)). Qed.
Lemma lem2289163 (h1 : term60) : term60.
Proof. exact (h1). Qed.
Lemma lem2289166 (h1 : term61) : term61.
Proof. exact (h1). Qed.
Lemma lem2289167 : term62.
Proof. exact (fun h0 : term61 => @lem2289166 h0). Qed.
Lemma lem2289168 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem2289169 (h1 : term61) : term61.
Proof. exact (h1). Qed.
Lemma lem2289170 (h1 : term61) (h2 : term62) : term61.
Proof. exact (@lem2289168 h2 (@lem2289169 h1)). Qed.
Lemma lem2289171 (h1 : term61) : term63.
Proof. exact (fun h0 : term62 => @lem2289170 h1 h0). Qed.
Lemma lem2289172 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem2289173 (h1 : term61) (h2 : term62) : term61.
Proof. exact (@lem2289171 h1 (@lem2289172 h2)). Qed.
Lemma lem2289174 (h1 : term62) : term62.
Proof. exact (fun h0 : term61 => @lem2289173 h0 h1). Qed.
Lemma lem2289175 : term64.
Proof. exact (fun h0 : term62 => @lem2289174 h0). Qed.
Lemma lem2289178 : term62.
Proof. exact (@lem2289175 (@lem2289167)). Qed.
Lemma lem2289182 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2289183 : term65 = term66.
Proof. exact (@lem2289182 term0). Qed.
Lemma lem2289189 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term67 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2289190 (P : nat -> Prop) (Q : nat -> Prop) : (term69 P Q) = (term70 P Q).
Proof. exact (@lem2289189 nat P Q). Qed.
Lemma lem2289191 (x : real) : (term71 x) = (term72 x).
Proof. exact (@lem2289190 (term73 x) (term74 x)). Qed.
Lemma lem2289192 (x : real) (n : nat) : (term75 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term75 x n)). Qed.
Lemma lem2289193 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2289194 (x : real) (n : nat) : (term76 x n) = (term77 x n).
Proof. exact (MK_COMB (@lem2289193) (@lem2289192 x n)). Qed.
Lemma lem2289195 (x : real) (n : nat) : (term78 x n) = (x = (term79 n)).
Proof. exact (eq_refl (term78 x n)). Qed.
Lemma lem2289196 (x : real) (n : nat) : (term80 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem2289194 x n) (@lem2289195 x n)). Qed.
Lemma lem2289197 (x : real) : (term82 x) = (term83 x).
Proof. exact (fun_ext (fun n : nat => @lem2289196 x n)). Qed.
Lemma lem2289198 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2289199 (x : real) : (term71 x) = (term84 x).
Proof. exact (MK_COMB (@lem2289198) (@lem2289197 x)). Qed.
Lemma lem2289200 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2289201 (x : real) : (term85 x) = (term86 x).
Proof. exact (MK_COMB (@lem2289200) (@lem2289199 x)). Qed.
Lemma lem2289202 (x : real) (n : nat) : (term75 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term75 x n)). Qed.
Lemma lem2289203 (x : real) : (term87 x) = (term73 x).
Proof. exact (fun_ext (fun n : nat => @lem2289202 x n)). Qed.
Lemma lem2289204 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2289205 (x : real) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem2289204) (@lem2289203 x)). Qed.
Lemma lem2289206 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2289207 (x : real) : (term90 x) = (term91 x).
Proof. exact (MK_COMB (@lem2289206) (@lem2289205 x)). Qed.
Lemma lem2289208 (x : real) (n : nat) : (term78 x n) = (x = (term79 n)).
Proof. exact (eq_refl (term78 x n)). Qed.
Lemma lem2289209 (x : real) : (term92 x) = (term74 x).
Proof. exact (fun_ext (fun n : nat => @lem2289208 x n)). Qed.
Lemma lem2289210 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2289211 (x : real) : (term93 x) = (term94 x).
Proof. exact (MK_COMB (@lem2289210) (@lem2289209 x)). Qed.
Lemma lem2289212 (x : real) : (term72 x) = (term95 x).
Proof. exact (MK_COMB (@lem2289207 x) (@lem2289211 x)). Qed.
Lemma lem2289213 (x : real) : ((term71 x) = (term72 x)) = ((term84 x) = (term95 x)).
Proof. exact (MK_COMB (@lem2289201 x) (@lem2289212 x)). Qed.
Lemma lem2289214 (x : real) : (term84 x) = (term95 x).
Proof. exact (EQ_MP (@lem2289213 x) (@lem2289191 x)). Qed.
Lemma lem2289225 (x : real) : (term96 x) = (term96 x).
Proof. exact (eq_refl (term96 x)). Qed.
Lemma lem2289226 (x : real) : ((integer x) = (term84 x)) = ((integer x) = (term95 x)).
Proof. exact (MK_COMB (@lem2289225 x) (@lem2289214 x)). Qed.
Lemma lem2289227 : term97 = term98.
Proof. exact (fun_ext (fun x : real => @lem2289226 x)). Qed.
Lemma lem2289228 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2289229 : term0 = term99.
Proof. exact (MK_COMB (@lem2289228) (@lem2289227)). Qed.
Lemma lem2289234 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2289235 : term66 = term100.
Proof. exact (MK_COMB (@lem2289234) (@lem2289229)). Qed.
Lemma lem2289236 : term65 = term100.
Proof. exact (TRANS (@lem2289183) (@lem2289235)). Qed.
Lemma lem2289237 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem2289244 : term61 = term102.
Proof. exact (MK_COMB (@lem2289237) (@lem2289236)). Qed.
Lemma lem2289245 (x : real) (n : nat) : (x = (term79 n)) = (x = (term79 n)).
Proof. exact (eq_refl (x = (term79 n))). Qed.
Lemma lem2289246 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun n : nat => @lem2289245 x n)). Qed.
Lemma lem2289247 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2289248 (x : real) : (term94 x) = (term94 x).
Proof. exact (MK_COMB (@lem2289247) (@lem2289246 x)). Qed.
Lemma lem2289249 (x : real) (n : nat) : (x = (real_of_num n)) = (x = (real_of_num n)).
Proof. exact (eq_refl (x = (real_of_num n))). Qed.
Lemma lem2289250 (x : real) : (term73 x) = (term73 x).
Proof. exact (fun_ext (fun n : nat => @lem2289249 x n)). Qed.
Lemma lem2289251 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2289252 (x : real) : (term89 x) = (term89 x).
Proof. exact (MK_COMB (@lem2289251) (@lem2289250 x)). Qed.
Lemma lem2289253 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2289254 (x : real) : (term91 x) = (term91 x).
Proof. exact (MK_COMB (@lem2289253) (@lem2289252 x)). Qed.
Lemma lem2289255 (x : real) : (term95 x) = (term95 x).
Proof. exact (MK_COMB (@lem2289254 x) (@lem2289248 x)). Qed.
Lemma lem2289258 (x : real) : (term96 x) = (term96 x).
Proof. exact (eq_refl (term96 x)). Qed.
Lemma lem2289259 (x : real) : ((integer x) = (term95 x)) = ((integer x) = (term95 x)).
Proof. exact (MK_COMB (@lem2289258 x) (@lem2289255 x)). Qed.
Lemma lem2289260 : term98 = term98.
Proof. exact (fun_ext (fun x : real => @lem2289259 x)). Qed.
Lemma lem2289261 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2289262 : term99 = term99.
Proof. exact (MK_COMB (@lem2289261) (@lem2289260)). Qed.
Lemma lem2289263 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2289264 : term100 = term100.
Proof. exact (MK_COMB (@lem2289263) (@lem2289262)). Qed.
Lemma lem2289269 : term101 = term101.
Proof. exact (eq_refl term101). Qed.
Lemma lem2289270 : term102 = term102.
Proof. exact (MK_COMB (@lem2289269) (@lem2289264)). Qed.
Lemma lem2289295 : term61 = term102.
Proof. exact (TRANS (@lem2289244) (@lem2289270)). Qed.
Lemma lem2289296 : term102 = term61.
Proof. exact (SYM (@lem2289295)). Qed.
Lemma lem2289298 (h1 : term99) : term99.
Proof. exact (h1). Qed.
Lemma lem2289304 (h1 : term60) : term60.
Proof. exact (h1). Qed.
Lemma lem2289308 (x : real) (n : nat) : (x = (real_of_num n)) = (x = (real_of_num n)).
Proof. exact (eq_refl (x = (real_of_num n))). Qed.
Lemma lem2289309 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem2289310 (x : real) : (term105 x) = (term106 x).
Proof. exact (@lem2289309 (term73 x)). Qed.
Lemma lem2289311 (x : real) (n : nat) : (term75 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term75 x n)). Qed.
Lemma lem2289312 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2289314 (x : real) (n : nat) : (term107 x n) = (term108 x n).
Proof. exact (MK_COMB (@lem2289312) (@lem2289311 x n)). Qed.
Lemma lem2289315 (x : real) : (term109 x) = (term110 x).
Proof. exact (fun_ext (fun n : nat => @lem2289314 x n)). Qed.
Lemma lem2289316 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2289317 (x : real) : (term106 x) = (term111 x).
Proof. exact (MK_COMB (@lem2289316) (@lem2289315 x)). Qed.
Lemma lem2289318 (x : real) : (term105 x) = (term111 x).
Proof. exact (TRANS (@lem2289310 x) (@lem2289317 x)). Qed.
Lemma lem2289319 (x : real) : (term73 x) = (term73 x).
Proof. exact (fun_ext (fun n : nat => @lem2289308 x n)). Qed.
Lemma lem2289320 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2289321 (x : real) : (term89 x) = (term89 x).
Proof. exact (MK_COMB (@lem2289320) (@lem2289319 x)). Qed.
Lemma lem2289323 (x : real) (n : nat) : (x = (term79 n)) = (x = (term79 n)).
Proof. exact (eq_refl (x = (term79 n))). Qed.
Lemma lem2289324 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem2289325 (x : real) : (term112 x) = (term113 x).
Proof. exact (@lem2289324 (term74 x)). Qed.
Lemma lem2289326 (x : real) (n : nat) : (term78 x n) = (x = (term79 n)).
Proof. exact (eq_refl (term78 x n)). Qed.
Lemma lem2289327 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2289329 (x : real) (n : nat) : (term114 x n) = (term115 x n).
Proof. exact (MK_COMB (@lem2289327) (@lem2289326 x n)). Qed.
Lemma lem2289330 (x : real) : (term116 x) = (term117 x).
Proof. exact (fun_ext (fun n : nat => @lem2289329 x n)). Qed.
Lemma lem2289331 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2289332 (x : real) : (term113 x) = (term118 x).
Proof. exact (MK_COMB (@lem2289331) (@lem2289330 x)). Qed.
Lemma lem2289333 (x : real) : (term112 x) = (term118 x).
Proof. exact (TRANS (@lem2289325 x) (@lem2289332 x)). Qed.
Lemma lem2289334 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun n : nat => @lem2289323 x n)). Qed.
Lemma lem2289335 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2289336 (x : real) : (term94 x) = (term94 x).
Proof. exact (MK_COMB (@lem2289335) (@lem2289334 x)). Qed.
Lemma lem2289337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2289338 (x : real) : (term119 x) = (term120 x).
Proof. exact (MK_COMB (@lem2289337) (@lem2289318 x)). Qed.
Lemma lem2289339 (x : real) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem2289338 x) (@lem2289333 x)). Qed.
Lemma lem2289340 (x : real) : (term123 x) = (term121 x).
Proof. exact (@lem17160 (term89 x) (term94 x)). Qed.
Lemma lem2289341 (x : real) : (term123 x) = (term122 x).
Proof. exact (TRANS (@lem2289340 x) (@lem2289339 x)). Qed.
Lemma lem2289342 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2289343 (x : real) : (term91 x) = (term91 x).
Proof. exact (MK_COMB (@lem2289342) (@lem2289321 x)). Qed.
Lemma lem2289344 (x : real) : (term95 x) = (term95 x).
Proof. exact (MK_COMB (@lem2289343 x) (@lem2289336 x)). Qed.
Lemma lem2289346 (x : real) : (term124 x) = (term124 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem2289347 (x : real) : (term125 x) = (term125 x).
Proof. exact (MK_COMB (@lem2289346 x) (@lem2289344 x)). Qed.
Lemma lem2289349 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem2289350 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem2289349 x) (@lem2289341 x)). Qed.
Lemma lem2289351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2289352 (x : real) : (term129 x) = (term130 x).
Proof. exact (MK_COMB (@lem2289351) (@lem2289350 x)). Qed.
Lemma lem2289353 (x : real) : (term131 x) = (term132 x).
Proof. exact (MK_COMB (@lem2289352 x) (@lem2289347 x)). Qed.
Lemma lem2289354 (x : real) : ((integer x) = (term95 x)) = (term131 x).
Proof. exact (@lem17784 (integer x) (term95 x)). Qed.
Lemma lem2289355 (x : real) : ((integer x) = (term95 x)) = (term132 x).
Proof. exact (TRANS (@lem2289354 x) (@lem2289353 x)). Qed.
Lemma lem2289356 : term98 = term133.
Proof. exact (fun_ext (fun x : real => @lem2289355 x)). Qed.
Lemma lem2289357 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2289358 : term99 = term134.
Proof. exact (MK_COMB (@lem2289357) (@lem2289356)). Qed.
Lemma lem2289360 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem2289361 (P : real -> Prop) (Q : real -> Prop) : (term137 P Q) = (term138 P Q).
Proof. exact (@lem2289360 real P Q). Qed.
Lemma lem2289362 : term139 = term140.
Proof. exact (@lem2289361 term141 term142). Qed.
Lemma lem2289363 (x : real) : (term143 x) = (term128 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem2289364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2289365 (x : real) : (term144 x) = (term130 x).
Proof. exact (MK_COMB (@lem2289364) (@lem2289363 x)). Qed.
Lemma lem2289366 (x : real) : (term145 x) = (term125 x).
Proof. exact (eq_refl (term145 x)). Qed.
Lemma lem2289367 (x : real) : (term146 x) = (term132 x).
Proof. exact (MK_COMB (@lem2289365 x) (@lem2289366 x)). Qed.
Lemma lem2289368 : term147 = term133.
Proof. exact (fun_ext (fun x : real => @lem2289367 x)). Qed.
Lemma lem2289369 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2289370 : term139 = term134.
Proof. exact (MK_COMB (@lem2289369) (@lem2289368)). Qed.
Lemma lem2289371 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2289372 : term148 = term149.
Proof. exact (MK_COMB (@lem2289371) (@lem2289370)). Qed.
Lemma lem2289373 (x : real) : (term143 x) = (term128 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem2289374 : term150 = term141.
Proof. exact (fun_ext (fun x : real => @lem2289373 x)). Qed.
Lemma lem2289375 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2289376 : term151 = term152.
Proof. exact (MK_COMB (@lem2289375) (@lem2289374)). Qed.
Lemma lem2289377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2289378 : term153 = term154.
Proof. exact (MK_COMB (@lem2289377) (@lem2289376)). Qed.
Lemma lem2289379 (x : real) : (term145 x) = (term125 x).
Proof. exact (eq_refl (term145 x)). Qed.
Lemma lem2289380 : term155 = term142.
Proof. exact (fun_ext (fun x : real => @lem2289379 x)). Qed.
Lemma lem2289381 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2289382 : term156 = term157.
Proof. exact (MK_COMB (@lem2289381) (@lem2289380)). Qed.
Lemma lem2289383 : term140 = term158.
Proof. exact (MK_COMB (@lem2289378) (@lem2289382)). Qed.
Lemma lem2289384 : (term139 = term140) = (term134 = term158).
Proof. exact (MK_COMB (@lem2289372) (@lem2289383)). Qed.
Lemma lem2289385 : term134 = term158.
Proof. exact (EQ_MP (@lem2289384) (@lem2289362)). Qed.
Lemma lem2289479 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term68 A P Q) = (term67 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2289480 (P : nat -> Prop) (Q : nat -> Prop) : (term70 P Q) = (term69 P Q).
Proof. exact (@lem2289479 nat P Q). Qed.
Lemma lem2289481 (x : real) : (term72 x) = (term71 x).
Proof. exact (@lem2289480 (term73 x) (term74 x)). Qed.
Lemma lem2289482 (x : real) (n : nat) : (term75 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term75 x n)). Qed.
Lemma lem2289483 (x : real) : (term87 x) = (term73 x).
Proof. exact (fun_ext (fun n : nat => @lem2289482 x n)). Qed.
Lemma lem2289484 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2289485 (x : real) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem2289484) (@lem2289483 x)). Qed.
Lemma lem2289486 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2289487 (x : real) : (term90 x) = (term91 x).
Proof. exact (MK_COMB (@lem2289486) (@lem2289485 x)). Qed.
Lemma lem2289488 (x : real) (n : nat) : (term78 x n) = (x = (term79 n)).
Proof. exact (eq_refl (term78 x n)). Qed.
Lemma lem2289489 (x : real) : (term92 x) = (term74 x).
Proof. exact (fun_ext (fun n : nat => @lem2289488 x n)). Qed.
Lemma lem2289490 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2289491 (x : real) : (term93 x) = (term94 x).
Proof. exact (MK_COMB (@lem2289490) (@lem2289489 x)). Qed.
Lemma lem2289492 (x : real) : (term72 x) = (term95 x).
Proof. exact (MK_COMB (@lem2289487 x) (@lem2289491 x)). Qed.
Lemma lem2289493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2289494 (x : real) : (term159 x) = (term160 x).
Proof. exact (MK_COMB (@lem2289493) (@lem2289492 x)). Qed.
Lemma lem2289495 (x : real) (n : nat) : (term75 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term75 x n)). Qed.
Lemma lem2289496 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2289497 (x : real) (n : nat) : (term76 x n) = (term77 x n).
Proof. exact (MK_COMB (@lem2289496) (@lem2289495 x n)). Qed.
Lemma lem2289498 (x : real) (n : nat) : (term78 x n) = (x = (term79 n)).
Proof. exact (eq_refl (term78 x n)). Qed.
Lemma lem2289499 (x : real) (n : nat) : (term80 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem2289497 x n) (@lem2289498 x n)). Qed.
Lemma lem2289500 (x : real) : (term82 x) = (term83 x).
Proof. exact (fun_ext (fun n : nat => @lem2289499 x n)). Qed.
Lemma lem2289501 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2289502 (x : real) : (term71 x) = (term84 x).
Proof. exact (MK_COMB (@lem2289501) (@lem2289500 x)). Qed.
Lemma lem2289503 (x : real) : ((term72 x) = (term71 x)) = ((term95 x) = (term84 x)).
Proof. exact (MK_COMB (@lem2289494 x) (@lem2289502 x)). Qed.
Lemma lem2289504 (x : real) : (term95 x) = (term84 x).
Proof. exact (EQ_MP (@lem2289503 x) (@lem2289481 x)). Qed.
Lemma lem2289505 (x : real) : (term124 x) = (term124 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem2289506 (x : real) : (term125 x) = (term161 x).
Proof. exact (MK_COMB (@lem2289505 x) (@lem2289504 x)). Qed.
Lemma lem2289508 {A : Type'} (P : Prop) (Q : A -> Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem2289509 (P : Prop) (Q : nat -> Prop) : (term164 P Q) = (term165 P Q).
Proof. exact (@lem2289508 nat P Q). Qed.
Lemma lem2289510 (x : real) : (term166 x) = (term167 x).
Proof. exact (@lem2289509 (term168 x) (term83 x)). Qed.
Lemma lem2289511 (x : real) (n : nat) : (term169 x n) = (term81 x n).
Proof. exact (eq_refl (term169 x n)). Qed.
Lemma lem2289512 (x : real) : (term170 x) = (term83 x).
Proof. exact (fun_ext (fun n : nat => @lem2289511 x n)). Qed.
Lemma lem2289513 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2289514 (x : real) : (term171 x) = (term84 x).
Proof. exact (MK_COMB (@lem2289513) (@lem2289512 x)). Qed.
Lemma lem2289515 (x : real) : (term124 x) = (term124 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem2289516 (x : real) : (term166 x) = (term161 x).
Proof. exact (MK_COMB (@lem2289515 x) (@lem2289514 x)). Qed.
Lemma lem2289517 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2289518 (x : real) : (term172 x) = (term173 x).
Proof. exact (MK_COMB (@lem2289517) (@lem2289516 x)). Qed.
Lemma lem2289519 (x : real) (n : nat) : (term169 x n) = (term81 x n).
Proof. exact (eq_refl (term169 x n)). Qed.
Lemma lem2289520 (x : real) : (term124 x) = (term124 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem2289521 (x : real) (n : nat) : (term174 x n) = (term175 x n).
Proof. exact (MK_COMB (@lem2289520 x) (@lem2289519 x n)). Qed.
Lemma lem2289522 (x : real) : (term176 x) = (term177 x).
Proof. exact (fun_ext (fun n : nat => @lem2289521 x n)). Qed.
Lemma lem2289523 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2289524 (x : real) : (term167 x) = (term178 x).
Proof. exact (MK_COMB (@lem2289523) (@lem2289522 x)). Qed.
Lemma lem2289525 (x : real) : ((term166 x) = (term167 x)) = ((term161 x) = (term178 x)).
Proof. exact (MK_COMB (@lem2289518 x) (@lem2289524 x)). Qed.
Lemma lem2289526 (x : real) : (term161 x) = (term178 x).
Proof. exact (EQ_MP (@lem2289525 x) (@lem2289510 x)). Qed.
Lemma lem2289527 (x : real) : (term125 x) = (term178 x).
Proof. exact (TRANS (@lem2289506 x) (@lem2289526 x)). Qed.
Lemma lem2289528 : term142 = term179.
Proof. exact (fun_ext (fun x : real => @lem2289527 x)). Qed.
Lemma lem2289529 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2289530 : term157 = term180.
Proof. exact (MK_COMB (@lem2289529) (@lem2289528)). Qed.
Lemma lem2289532 {A B : Type'} (P : type1413 A B) : (term181 A B P) = (term182 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem2289533 (P : type1622) : (term183 P) = (term184 P).
Proof. exact (@lem2289532 real nat P). Qed.
Lemma lem2289534 : term185 = term186.
Proof. exact (@lem2289533 term187). Qed.
Lemma lem2289535 (x : real) : (term188 x) = (term177 x).
Proof. exact (eq_refl (term188 x)). Qed.
Lemma lem2289536 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2289537 (x : real) (n : nat) : (term189 x n) = (term190 x n).
Proof. exact (MK_COMB (@lem2289535 x) (@lem2289536 n)). Qed.
Lemma lem2289538 (x : real) (n : nat) : (term190 x n) = (term175 x n).
Proof. exact (eq_refl (term190 x n)). Qed.
Lemma lem2289539 (x : real) (n : nat) : (term189 x n) = (term175 x n).
Proof. exact (TRANS (@lem2289537 x n) (@lem2289538 x n)). Qed.
Lemma lem2289540 (x : real) : (term191 x) = (term177 x).
Proof. exact (fun_ext (fun n : nat => @lem2289539 x n)). Qed.
Lemma lem2289541 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2289542 (x : real) : (term192 x) = (term178 x).
Proof. exact (MK_COMB (@lem2289541) (@lem2289540 x)). Qed.
Lemma lem2289543 : term193 = term179.
Proof. exact (fun_ext (fun x : real => @lem2289542 x)). Qed.
Lemma lem2289544 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2289545 : term185 = term180.
Proof. exact (MK_COMB (@lem2289544) (@lem2289543)). Qed.
Lemma lem2289546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2289547 : term194 = term195.
Proof. exact (MK_COMB (@lem2289546) (@lem2289545)). Qed.
Lemma lem2289548 (x : real) : (term188 x) = (term177 x).
Proof. exact (eq_refl (term188 x)). Qed.
Lemma lem2289549 (n : real -> nat) (x : real) : (n x) = (n x).
Proof. exact (eq_refl (n x)). Qed.
Lemma lem2289550 (n : real -> nat) (x : real) : (term196 n x) = (term197 n x).
Proof. exact (MK_COMB (@lem2289548 x) (@lem2289549 n x)). Qed.
Lemma lem2289551 (n : real -> nat) (x : real) : (term197 n x) = (term198 n x).
Proof. exact (eq_refl (term197 n x)). Qed.
Lemma lem2289552 (n : real -> nat) (x : real) : (term196 n x) = (term198 n x).
Proof. exact (TRANS (@lem2289550 n x) (@lem2289551 n x)). Qed.
Lemma lem2289553 (n : real -> nat) : (term199 n) = (term200 n).
Proof. exact (fun_ext (fun x : real => @lem2289552 n x)). Qed.
Lemma lem2289554 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2289555 (n : real -> nat) : (term201 n) = (term202 n).
Proof. exact (MK_COMB (@lem2289554) (@lem2289553 n)). Qed.
Lemma lem2289556 : term203 = term204.
Proof. exact (fun_ext (fun n : real -> nat => @lem2289555 n)). Qed.
Lemma lem2289557 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem2289558 : term186 = term205.
Proof. exact (MK_COMB (@lem2289557) (@lem2289556)). Qed.
Lemma lem2289559 : (term185 = term186) = (term180 = term205).
Proof. exact (MK_COMB (@lem2289547) (@lem2289558)). Qed.
Lemma lem2289560 : term180 = term205.
Proof. exact (EQ_MP (@lem2289559) (@lem2289534)). Qed.
Lemma lem2289561 : term157 = term205.
Proof. exact (TRANS (@lem2289530) (@lem2289560)). Qed.
Lemma lem2289562 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem2289563 : term158 = term206.
Proof. exact (MK_COMB (@lem2289562) (@lem2289561)). Qed.
Lemma lem2289565 {A : Type'} (P : Prop) (Q : A -> Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem2289566 (P : Prop) (Q : type1024) : (term209 P Q) = (term210 P Q).
Proof. exact (@lem2289565 (real -> nat) P Q). Qed.
Lemma lem2289567 : term211 = term212.
Proof. exact (@lem2289566 term152 term204). Qed.
Lemma lem2289568 (n : real -> nat) : (term213 n) = (term202 n).
Proof. exact (eq_refl (term213 n)). Qed.
Lemma lem2289569 : term214 = term204.
Proof. exact (fun_ext (fun n : real -> nat => @lem2289568 n)). Qed.
Lemma lem2289570 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem2289571 : term215 = term205.
Proof. exact (MK_COMB (@lem2289570) (@lem2289569)). Qed.
Lemma lem2289572 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem2289573 : term211 = term206.
Proof. exact (MK_COMB (@lem2289572) (@lem2289571)). Qed.
Lemma lem2289574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2289575 : term216 = term217.
Proof. exact (MK_COMB (@lem2289574) (@lem2289573)). Qed.
Lemma lem2289576 (n : real -> nat) : (term213 n) = (term202 n).
Proof. exact (eq_refl (term213 n)). Qed.
Lemma lem2289577 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem2289578 (n : real -> nat) : (term218 n) = (term219 n).
Proof. exact (MK_COMB (@lem2289577) (@lem2289576 n)). Qed.
Lemma lem2289579 : term220 = term221.
Proof. exact (fun_ext (fun n : real -> nat => @lem2289578 n)). Qed.
Lemma lem2289580 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem2289581 : term212 = term222.
Proof. exact (MK_COMB (@lem2289580) (@lem2289579)). Qed.
Lemma lem2289582 : (term211 = term212) = (term206 = term222).
Proof. exact (MK_COMB (@lem2289575) (@lem2289581)). Qed.
Lemma lem2289583 : term206 = term222.
Proof. exact (EQ_MP (@lem2289582) (@lem2289567)). Qed.
Lemma lem2289584 : term158 = term222.
Proof. exact (TRANS (@lem2289563) (@lem2289583)). Qed.
Lemma lem2289585 : term134 = term222.
Proof. exact (TRANS (@lem2289385) (@lem2289584)). Qed.
Lemma lem2289586 : term99 = term222.
Proof. exact (TRANS (@lem2289358) (@lem2289585)). Qed.
Lemma lem2289587 (h1 : term99) : term222.
Proof. exact (EQ_MP (@lem2289586) (@lem2289298 h1)). Qed.
Lemma lem2289588 (n : real -> nat) (h1 : term219 n) : term219 n.
Proof. exact (h1). Qed.
Lemma lem2289600 (h1 : term60) : term60.
Proof. exact (h1). Qed.
Lemma lem2289631 (n : real -> nat) (x : real) : (term198 n x) = (term198 n x).
Proof. exact (eq_refl (term198 n x)). Qed.
Lemma lem2289632 (n : real -> nat) : (term200 n) = (term200 n).
Proof. exact (fun_ext (fun x : real => @lem2289631 n x)). Qed.
Lemma lem2289633 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2289634 (n : real -> nat) : (term202 n) = (term202 n).
Proof. exact (MK_COMB (@lem2289633) (@lem2289632 n)). Qed.
Lemma lem2289645 (x : real) (n : nat) : (term115 x n) = (term115 x n).
Proof. exact (eq_refl (term115 x n)). Qed.
Lemma lem2289646 (x : real) : (term117 x) = (term117 x).
Proof. exact (fun_ext (fun n : nat => @lem2289645 x n)). Qed.
Lemma lem2289647 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2289648 (x : real) : (term118 x) = (term118 x).
Proof. exact (MK_COMB (@lem2289647) (@lem2289646 x)). Qed.
Lemma lem2289657 (x : real) (n : nat) : (term108 x n) = (term108 x n).
Proof. exact (eq_refl (term108 x n)). Qed.
Lemma lem2289658 (x : real) : (term110 x) = (term110 x).
Proof. exact (fun_ext (fun n : nat => @lem2289657 x n)). Qed.
Lemma lem2289659 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2289660 (x : real) : (term111 x) = (term111 x).
Proof. exact (MK_COMB (@lem2289659) (@lem2289658 x)). Qed.
Lemma lem2289661 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2289662 (x : real) : (term120 x) = (term120 x).
Proof. exact (MK_COMB (@lem2289661) (@lem2289660 x)). Qed.
Lemma lem2289663 (x : real) : (term122 x) = (term122 x).
Proof. exact (MK_COMB (@lem2289662 x) (@lem2289648 x)). Qed.
Lemma lem2289668 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem2289669 (x : real) : (term128 x) = (term128 x).
Proof. exact (MK_COMB (@lem2289668 x) (@lem2289663 x)). Qed.
Lemma lem2289670 : term141 = term141.
Proof. exact (fun_ext (fun x : real => @lem2289669 x)). Qed.
Lemma lem2289671 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2289672 : term152 = term152.
Proof. exact (MK_COMB (@lem2289671) (@lem2289670)). Qed.
Lemma lem2289673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2289674 : term154 = term154.
Proof. exact (MK_COMB (@lem2289673) (@lem2289672)). Qed.
Lemma lem2289675 (n : real -> nat) : (term219 n) = (term219 n).
Proof. exact (MK_COMB (@lem2289674) (@lem2289634 n)). Qed.
Lemma lem2289676 (n : real -> nat) (h1 : term219 n) : term219 n.
Proof. exact (EQ_MP (@lem2289675 n) (@lem2289588 n h1)). Qed.
Lemma lem2289678 (n : real -> nat) (h1 : term219 n) : term152.
Proof. exact (proj1 (@lem2289676 n h1)). Qed.
Lemma lem2289682 (h1 : term60) : term60.
Proof. exact (h1). Qed.
Lemma lem2289684 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem2289685 (P : nat -> Prop) (Q : nat -> Prop) : (term223 P Q) = (term224 P Q).
Proof. exact (@lem2289684 nat P Q). Qed.
Lemma lem2289686 (x : real) : (term225 x) = (term226 x).
Proof. exact (@lem2289685 (term110 x) (term117 x)). Qed.
Lemma lem2289687 (x : real) (n : nat) : (term227 x n) = (term108 x n).
Proof. exact (eq_refl (term227 x n)). Qed.
Lemma lem2289688 (x : real) : (term228 x) = (term110 x).
Proof. exact (fun_ext (fun n : nat => @lem2289687 x n)). Qed.
Lemma lem2289689 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2289690 (x : real) : (term229 x) = (term111 x).
Proof. exact (MK_COMB (@lem2289689) (@lem2289688 x)). Qed.
Lemma lem2289691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2289692 (x : real) : (term230 x) = (term120 x).
Proof. exact (MK_COMB (@lem2289691) (@lem2289690 x)). Qed.
Lemma lem2289693 (x : real) (n : nat) : (term231 x n) = (term115 x n).
Proof. exact (eq_refl (term231 x n)). Qed.
Lemma lem2289694 (x : real) : (term232 x) = (term117 x).
Proof. exact (fun_ext (fun n : nat => @lem2289693 x n)). Qed.
Lemma lem2289695 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2289696 (x : real) : (term233 x) = (term118 x).
Proof. exact (MK_COMB (@lem2289695) (@lem2289694 x)). Qed.
Lemma lem2289697 (x : real) : (term225 x) = (term122 x).
Proof. exact (MK_COMB (@lem2289692 x) (@lem2289696 x)). Qed.
Lemma lem2289698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2289699 (x : real) : (term234 x) = (term235 x).
Proof. exact (MK_COMB (@lem2289698) (@lem2289697 x)). Qed.
Lemma lem2289700 (x : real) (n : nat) : (term227 x n) = (term108 x n).
Proof. exact (eq_refl (term227 x n)). Qed.
Lemma lem2289701 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2289702 (x : real) (n : nat) : (term236 x n) = (term237 x n).
Proof. exact (MK_COMB (@lem2289701) (@lem2289700 x n)). Qed.
Lemma lem2289703 (x : real) (n : nat) : (term231 x n) = (term115 x n).
Proof. exact (eq_refl (term231 x n)). Qed.
Lemma lem2289704 (x : real) (n : nat) : (term238 x n) = (term239 x n).
Proof. exact (MK_COMB (@lem2289702 x n) (@lem2289703 x n)). Qed.
Lemma lem2289705 (x : real) : (term240 x) = (term241 x).
Proof. exact (fun_ext (fun n : nat => @lem2289704 x n)). Qed.
Lemma lem2289706 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2289707 (x : real) : (term226 x) = (term242 x).
Proof. exact (MK_COMB (@lem2289706) (@lem2289705 x)). Qed.
Lemma lem2289708 (x : real) : ((term225 x) = (term226 x)) = ((term122 x) = (term242 x)).
Proof. exact (MK_COMB (@lem2289699 x) (@lem2289707 x)). Qed.
Lemma lem2289709 (x : real) : (term122 x) = (term242 x).
Proof. exact (EQ_MP (@lem2289708 x) (@lem2289686 x)). Qed.
Lemma lem2289710 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem2289711 (x : real) : (term128 x) = (term243 x).
Proof. exact (MK_COMB (@lem2289710 x) (@lem2289709 x)). Qed.
Lemma lem2289713 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem2289714 (P : Prop) (Q : nat -> Prop) : (term246 P Q) = (term247 P Q).
Proof. exact (@lem2289713 nat P Q). Qed.
Lemma lem2289715 (x : real) : (term248 x) = (term249 x).
Proof. exact (@lem2289714 (integer x) (term241 x)). Qed.
Lemma lem2289716 (x : real) (n : nat) : (term250 x n) = (term239 x n).
Proof. exact (eq_refl (term250 x n)). Qed.
Lemma lem2289717 (x : real) : (term251 x) = (term241 x).
Proof. exact (fun_ext (fun n : nat => @lem2289716 x n)). Qed.
Lemma lem2289718 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2289719 (x : real) : (term252 x) = (term242 x).
Proof. exact (MK_COMB (@lem2289718) (@lem2289717 x)). Qed.
Lemma lem2289720 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem2289721 (x : real) : (term248 x) = (term243 x).
Proof. exact (MK_COMB (@lem2289720 x) (@lem2289719 x)). Qed.
Lemma lem2289722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2289723 (x : real) : (term253 x) = (term254 x).
Proof. exact (MK_COMB (@lem2289722) (@lem2289721 x)). Qed.
Lemma lem2289724 (x : real) (n : nat) : (term250 x n) = (term239 x n).
Proof. exact (eq_refl (term250 x n)). Qed.
Lemma lem2289725 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem2289726 (x : real) (n : nat) : (term255 x n) = (term256 x n).
Proof. exact (MK_COMB (@lem2289725 x) (@lem2289724 x n)). Qed.
Lemma lem2289727 (x : real) : (term257 x) = (term258 x).
Proof. exact (fun_ext (fun n : nat => @lem2289726 x n)). Qed.
Lemma lem2289728 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2289729 (x : real) : (term249 x) = (term259 x).
Proof. exact (MK_COMB (@lem2289728) (@lem2289727 x)). Qed.
Lemma lem2289730 (x : real) : ((term248 x) = (term249 x)) = ((term243 x) = (term259 x)).
Proof. exact (MK_COMB (@lem2289723 x) (@lem2289729 x)). Qed.
Lemma lem2289731 (x : real) : (term243 x) = (term259 x).
Proof. exact (EQ_MP (@lem2289730 x) (@lem2289715 x)). Qed.
Lemma lem2289732 (x : real) : (term128 x) = (term259 x).
Proof. exact (TRANS (@lem2289711 x) (@lem2289731 x)). Qed.
Lemma lem2289733 : term141 = term260.
Proof. exact (fun_ext (fun x : real => @lem2289732 x)). Qed.
Lemma lem2289734 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2289735 : term152 = term261.
Proof. exact (MK_COMB (@lem2289734) (@lem2289733)). Qed.
Lemma lem2289752 (x : real) (n : nat) : (term256 x n) = (term262 x n).
Proof. exact (@lem19490 (term108 x n) (integer x) (term115 x n)). Qed.
Lemma lem2289753 (x : real) : (term258 x) = (term263 x).
Proof. exact (fun_ext (fun n : nat => @lem2289752 x n)). Qed.
Lemma lem2289754 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2289755 (x : real) : (term259 x) = (term264 x).
Proof. exact (MK_COMB (@lem2289754) (@lem2289753 x)). Qed.
Lemma lem2289756 : term260 = term265.
Proof. exact (fun_ext (fun x : real => @lem2289755 x)). Qed.
Lemma lem2289757 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2289758 : term261 = term266.
Proof. exact (MK_COMB (@lem2289757) (@lem2289756)). Qed.
Lemma lem2289759 : term152 = term266.
Proof. exact (TRANS (@lem2289735) (@lem2289758)). Qed.
Lemma lem2289760 (n : real -> nat) (h1 : term219 n) : term266.
Proof. exact (EQ_MP (@lem2289759) (@lem2289678 n h1)). Qed.
Lemma lem2289780 (_28768 : real) (n : real -> nat) (h1 : term219 n) : term267 _28768.
Proof. exact (@lem2289760 n h1 _28768). Qed.
Lemma lem2289781 (_28768 : real) : (term267 _28768) = (term264 _28768).
Proof. exact (eq_refl (term267 _28768)). Qed.
Lemma lem2289782 (_28768 : real) (n : real -> nat) (h1 : term219 n) : term264 _28768.
Proof. exact (EQ_MP (@lem2289781 _28768) (@lem2289780 _28768 n h1)). Qed.
Lemma lem2289783 (_28768 : real) (_28769 : nat) (n : real -> nat) (h1 : term219 n) : term268 _28768 _28769.
Proof. exact (@lem2289782 _28768 n h1 _28769). Qed.
Lemma lem2289784 (_28768 : real) (_28769 : nat) : (term268 _28768 _28769) = (term262 _28768 _28769).
Proof. exact (eq_refl (term268 _28768 _28769)). Qed.
Lemma lem2289785 (_28768 : real) (_28769 : nat) (n : real -> nat) (h1 : term219 n) : term262 _28768 _28769.
Proof. exact (EQ_MP (@lem2289784 _28768 _28769) (@lem2289783 _28768 _28769 n h1)). Qed.
Lemma lem2289792 (h1 : term60) : term60.
Proof. exact (h1). Qed.
Lemma lem2289808 (_28768 : real) (_28769 : nat) (n : real -> nat) (h1 : term219 n) : term269 _28768 _28769.
Proof. exact (proj1 (@lem2289785 _28768 _28769 n h1)). Qed.
Lemma lem2289872 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem2289873 : term21 = term21.
Proof. exact (@lem2289872 term21). Qed.
Lemma lem2289874 : term270.
Proof. exact (fun h0 : term271 => @lem2289873). Qed.
Lemma lem2289876 (p : Prop) : (term272 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2289877 : term270 = (term21 = term21).
Proof. exact (@lem2289876 (term21 = term21)). Qed.
Lemma lem2289878 : term21 = term21.
Proof. exact (EQ_MP (@lem2289877) (@lem2289874)). Qed.
Lemma lem2289880 (b : Prop) (a : Prop) : (a \/ b) = (term273 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2289881 (_28769 : nat) (_28768 : real) : (term269 _28768 _28769) = (term274 _28769 _28768).
Proof. exact (@lem2289880 (term108 _28768 _28769) (integer _28768)). Qed.
Lemma lem2289883 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2289884 (_28768 : real) (_28769 : nat) : (term276 _28768 _28769) = (_28768 = (real_of_num _28769)).
Proof. exact (@lem2289883 (_28768 = (real_of_num _28769))). Qed.
Lemma lem2289885 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2289886 (_28768 : real) (_28769 : nat) : (term277 _28768 _28769) = (term278 _28768 _28769).
Proof. exact (MK_COMB (@lem2289885) (@lem2289884 _28768 _28769)). Qed.
Lemma lem2289887 (_28768 : real) : (integer _28768) = (integer _28768).
Proof. exact (eq_refl (integer _28768)). Qed.
Lemma lem2289888 (_28769 : nat) (_28768 : real) : (term274 _28769 _28768) = (term279 _28769 _28768).
Proof. exact (MK_COMB (@lem2289886 _28768 _28769) (@lem2289887 _28768)). Qed.
Lemma lem2289889 (_28769 : nat) (_28768 : real) : (term269 _28768 _28769) = (term279 _28769 _28768).
Proof. exact (TRANS (@lem2289881 _28769 _28768) (@lem2289888 _28769 _28768)). Qed.
Lemma lem2289892 (_28769 : nat) (_28768 : real) (n : real -> nat) (h1 : term219 n) : term279 _28769 _28768.
Proof. exact (EQ_MP (@lem2289889 _28769 _28768) (@lem2289808 _28768 _28769 n h1)). Qed.
Lemma lem2289893 (n : real -> nat) (h1 : term219 n) : term280.
Proof. exact (@lem2289892 term281 term21 n h1). Qed.
Lemma lem2289896 (n : real -> nat) (h1 : term219 n) : term30.
Proof. exact (@lem2289893 n h1 (@lem2289878)). Qed.
Lemma lem2289897 (n : real -> nat) (h1 : term219 n) : term282.
Proof. exact (fun h0 : term60 => @lem2289896 n h1). Qed.
Lemma lem2289899 (p : Prop) : (term272 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2289900 : term282 = term30.
Proof. exact (@lem2289899 term30). Qed.
Lemma lem2289901 (n : real -> nat) (h1 : term219 n) : term30.
Proof. exact (EQ_MP (@lem2289900) (@lem2289897 n h1)). Qed.
Lemma lem2289904 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2289906 : term60 = term283.
Proof. exact (@lem2289904 term30). Qed.
Lemma lem2289909 (h1 : term60) : term283.
Proof. exact (EQ_MP (@lem2289906) (@lem2289792 h1)). Qed.
Lemma lem2289912 (n : real -> nat) (h1 : term60) (h2 : term219 n) : False.
Proof. exact (@lem2289909 h1 (@lem2289901 n h2)). Qed.
Lemma lem2289913 (n : real -> nat) (h1 : term60) (h2 : term219 n) : term284.
Proof. exact (fun h0 : ~ False => @lem2289912 n h1 h2). Qed.
Lemma lem2289915 (p : Prop) : (term272 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2289916 : term284 = False.
Proof. exact (@lem2289915 False). Qed.
Lemma lem2289917 (n : real -> nat) (h1 : term60) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2289916) (@lem2289913 n h1 h2)). Qed.
Lemma lem2289918 (n : real -> nat) (h1 : term60) (h2 : term219 n) : term60 = False.
Proof. exact (prop_ext (fun h3 : term60 => @lem2289917 n h1 h2) (fun h3 : False => @lem2289792 h1)). Qed.
Lemma lem2289919 (n : real -> nat) (h1 : term60) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2289918 n h1 h2) (@lem2289792 h1)). Qed.
Lemma lem2289920 (n : real -> nat) (h1 : term60) (h2 : term219 n) : term60 = False.
Proof. exact (prop_ext (fun h3 : term60 => @lem2289919 n h1 h2) (fun h3 : False => @lem2289682 h1)). Qed.
Lemma lem2289921 (n : real -> nat) (h1 : term60) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2289920 n h1 h2) (@lem2289682 h1)). Qed.
Lemma lem2289922 (n : real -> nat) (h1 : term60) (h2 : term219 n) : term60 = False.
Proof. exact (prop_ext (fun h3 : term60 => @lem2289921 n h1 h2) (fun h3 : False => @lem2289682 h1)). Qed.
Lemma lem2289923 (n : real -> nat) (h1 : term60) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2289922 n h1 h2) (@lem2289682 h1)). Qed.
Lemma lem2289924 (n : real -> nat) (h1 : term60) (h2 : term219 n) : (term219 n) = False.
Proof. exact (prop_ext (fun h3 : term219 n => @lem2289923 n h1 h2) (fun h3 : False => @lem2289676 n h2)). Qed.
Lemma lem2289925 (n : real -> nat) (h1 : term60) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2289924 n h1 h2) (@lem2289676 n h2)). Qed.
Lemma lem2289926 (n : real -> nat) (h1 : term60) (h2 : term219 n) : term60 = False.
Proof. exact (prop_ext (fun h3 : term60 => @lem2289925 n h1 h2) (fun h3 : False => @lem2289600 h1)). Qed.
Lemma lem2289927 (n : real -> nat) (h1 : term60) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2289926 n h1 h2) (@lem2289600 h1)). Qed.
Lemma lem2289928 (h1 : term99) (h2 : term60) : False.
Proof. exact (ex_elim (@lem2289587 h1) (fun n : real -> nat => fun h0 : term221 n => @lem2289927 n h2 h0)). Qed.
Lemma lem2289929 (h1 : term99) (h2 : term60) : term60 = False.
Proof. exact (prop_ext (fun h3 : term60 => @lem2289928 h1 h2) (fun h3 : False => @lem2289304 h2)). Qed.
Lemma lem2289930 (h1 : term99) (h2 : term60) : False.
Proof. exact (EQ_MP (@lem2289929 h1 h2) (@lem2289304 h2)). Qed.
Lemma lem2289931 (h1 : term60) : term285.
Proof. exact (fun h0 : term99 => @lem2289930 h0 h1). Qed.
Lemma lem2289932 : term285 = term100.
Proof. exact (@lem69 term99). Qed.
Lemma lem2289933 (h1 : term60) : term100.
Proof. exact (EQ_MP (@lem2289932) (@lem2289931 h1)). Qed.
Lemma lem2289934 : term102.
Proof. exact (fun h0 : term60 => @lem2289933 h0). Qed.
Lemma lem2289935 : term61.
Proof. exact (EQ_MP (@lem2289296) (@lem2289934)). Qed.
Lemma lem2289937 : term61.
Proof. exact (@lem2289178 (@lem2289935)). Qed.
Lemma lem2289938 (h1 : term60) : term65.
Proof. exact (@lem2289937 (@lem2289163 h1)). Qed.
Lemma lem2289939 (h1 : term60) : False.
Proof. exact (@lem2289938 h1 (@lem2288999)). Qed.
Lemma lem2289940 (h1 : term60) : term60 = False.
Proof. exact (prop_ext (fun h2 : term60 => @lem2289939 h1) (fun h2 : False => @lem2289163 h1)). Qed.
Lemma lem2289941 (h1 : term60) : False.
Proof. exact (EQ_MP (@lem2289940 h1) (@lem2289163 h1)). Qed.
Lemma lem2289942 : term59.
Proof. exact (fun h0 : term60 => @lem2289941 h0). Qed.
Lemma lem2289945 (p : Prop) : p = (term58 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2289946 : term49 = term286.
Proof. exact (@lem2289945 term49). Qed.
Lemma lem2289947 : term286 = term49.
Proof. exact (SYM (@lem2289946)). Qed.
Lemma lem2289948 (h1 : term287) : term287.
Proof. exact (h1). Qed.
Lemma lem2289951 (h1 : term288) : term288.
Proof. exact (h1). Qed.
Lemma lem2289952 : term289.
Proof. exact (fun h0 : term288 => @lem2289951 h0). Qed.
Lemma lem2289953 (h1 : term289) : term289.
Proof. exact (h1). Qed.
Lemma lem2289954 (h1 : term288) : term288.
Proof. exact (h1). Qed.
Lemma lem2289955 (h1 : term288) (h2 : term289) : term288.
Proof. exact (@lem2289953 h2 (@lem2289954 h1)). Qed.
Lemma lem2289956 (h1 : term288) : term290.
Proof. exact (fun h0 : term289 => @lem2289955 h1 h0). Qed.
Lemma lem2289957 (h1 : term289) : term289.
Proof. exact (h1). Qed.
Lemma lem2289958 (h1 : term288) (h2 : term289) : term288.
Proof. exact (@lem2289956 h1 (@lem2289957 h2)). Qed.
Lemma lem2289959 (h1 : term289) : term289.
Proof. exact (fun h0 : term288 => @lem2289958 h0 h1). Qed.
Lemma lem2289960 : term291.
Proof. exact (fun h0 : term289 => @lem2289959 h0). Qed.
Lemma lem2289963 : term289.
Proof. exact (@lem2289960 (@lem2289952)). Qed.
Lemma lem2289967 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2289968 : term65 = term66.
Proof. exact (@lem2289967 term0). Qed.
Lemma lem2289974 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term67 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2289975 (P : nat -> Prop) (Q : nat -> Prop) : (term69 P Q) = (term70 P Q).
Proof. exact (@lem2289974 nat P Q). Qed.
Lemma lem2289976 (x : real) : (term71 x) = (term72 x).
Proof. exact (@lem2289975 (term73 x) (term74 x)). Qed.
Lemma lem2289977 (x : real) (n : nat) : (term75 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term75 x n)). Qed.
Lemma lem2289978 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2289979 (x : real) (n : nat) : (term76 x n) = (term77 x n).
Proof. exact (MK_COMB (@lem2289978) (@lem2289977 x n)). Qed.
Lemma lem2289980 (x : real) (n : nat) : (term78 x n) = (x = (term79 n)).
Proof. exact (eq_refl (term78 x n)). Qed.
Lemma lem2289981 (x : real) (n : nat) : (term80 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem2289979 x n) (@lem2289980 x n)). Qed.
Lemma lem2289982 (x : real) : (term82 x) = (term83 x).
Proof. exact (fun_ext (fun n : nat => @lem2289981 x n)). Qed.
Lemma lem2289983 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2289984 (x : real) : (term71 x) = (term84 x).
Proof. exact (MK_COMB (@lem2289983) (@lem2289982 x)). Qed.
Lemma lem2289985 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2289986 (x : real) : (term85 x) = (term86 x).
Proof. exact (MK_COMB (@lem2289985) (@lem2289984 x)). Qed.
Lemma lem2289987 (x : real) (n : nat) : (term75 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term75 x n)). Qed.
Lemma lem2289988 (x : real) : (term87 x) = (term73 x).
Proof. exact (fun_ext (fun n : nat => @lem2289987 x n)). Qed.
Lemma lem2289989 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2289990 (x : real) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem2289989) (@lem2289988 x)). Qed.
Lemma lem2289991 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2289992 (x : real) : (term90 x) = (term91 x).
Proof. exact (MK_COMB (@lem2289991) (@lem2289990 x)). Qed.
Lemma lem2289993 (x : real) (n : nat) : (term78 x n) = (x = (term79 n)).
Proof. exact (eq_refl (term78 x n)). Qed.
Lemma lem2289994 (x : real) : (term92 x) = (term74 x).
Proof. exact (fun_ext (fun n : nat => @lem2289993 x n)). Qed.
Lemma lem2289995 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2289996 (x : real) : (term93 x) = (term94 x).
Proof. exact (MK_COMB (@lem2289995) (@lem2289994 x)). Qed.
Lemma lem2289997 (x : real) : (term72 x) = (term95 x).
Proof. exact (MK_COMB (@lem2289992 x) (@lem2289996 x)). Qed.
Lemma lem2289998 (x : real) : ((term71 x) = (term72 x)) = ((term84 x) = (term95 x)).
Proof. exact (MK_COMB (@lem2289986 x) (@lem2289997 x)). Qed.
Lemma lem2289999 (x : real) : (term84 x) = (term95 x).
Proof. exact (EQ_MP (@lem2289998 x) (@lem2289976 x)). Qed.
Lemma lem2290010 (x : real) : (term96 x) = (term96 x).
Proof. exact (eq_refl (term96 x)). Qed.
Lemma lem2290011 (x : real) : ((integer x) = (term84 x)) = ((integer x) = (term95 x)).
Proof. exact (MK_COMB (@lem2290010 x) (@lem2289999 x)). Qed.
Lemma lem2290012 : term97 = term98.
Proof. exact (fun_ext (fun x : real => @lem2290011 x)). Qed.
Lemma lem2290013 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290014 : term0 = term99.
Proof. exact (MK_COMB (@lem2290013) (@lem2290012)). Qed.
Lemma lem2290019 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2290020 : term66 = term100.
Proof. exact (MK_COMB (@lem2290019) (@lem2290014)). Qed.
Lemma lem2290021 : term65 = term100.
Proof. exact (TRANS (@lem2289968) (@lem2290020)). Qed.
Lemma lem2290022 : term292 = term292.
Proof. exact (eq_refl term292). Qed.
Lemma lem2290029 : term288 = term293.
Proof. exact (MK_COMB (@lem2290022) (@lem2290021)). Qed.
Lemma lem2290030 (x : real) (n : nat) : (x = (term79 n)) = (x = (term79 n)).
Proof. exact (eq_refl (x = (term79 n))). Qed.
Lemma lem2290031 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun n : nat => @lem2290030 x n)). Qed.
Lemma lem2290032 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290033 (x : real) : (term94 x) = (term94 x).
Proof. exact (MK_COMB (@lem2290032) (@lem2290031 x)). Qed.
Lemma lem2290034 (x : real) (n : nat) : (x = (real_of_num n)) = (x = (real_of_num n)).
Proof. exact (eq_refl (x = (real_of_num n))). Qed.
Lemma lem2290035 (x : real) : (term73 x) = (term73 x).
Proof. exact (fun_ext (fun n : nat => @lem2290034 x n)). Qed.
Lemma lem2290036 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290037 (x : real) : (term89 x) = (term89 x).
Proof. exact (MK_COMB (@lem2290036) (@lem2290035 x)). Qed.
Lemma lem2290038 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2290039 (x : real) : (term91 x) = (term91 x).
Proof. exact (MK_COMB (@lem2290038) (@lem2290037 x)). Qed.
Lemma lem2290040 (x : real) : (term95 x) = (term95 x).
Proof. exact (MK_COMB (@lem2290039 x) (@lem2290033 x)). Qed.
Lemma lem2290043 (x : real) : (term96 x) = (term96 x).
Proof. exact (eq_refl (term96 x)). Qed.
Lemma lem2290044 (x : real) : ((integer x) = (term95 x)) = ((integer x) = (term95 x)).
Proof. exact (MK_COMB (@lem2290043 x) (@lem2290040 x)). Qed.
Lemma lem2290045 : term98 = term98.
Proof. exact (fun_ext (fun x : real => @lem2290044 x)). Qed.
Lemma lem2290046 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290047 : term99 = term99.
Proof. exact (MK_COMB (@lem2290046) (@lem2290045)). Qed.
Lemma lem2290048 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2290049 : term100 = term100.
Proof. exact (MK_COMB (@lem2290048) (@lem2290047)). Qed.
Lemma lem2290054 : term292 = term292.
Proof. exact (eq_refl term292). Qed.
Lemma lem2290055 : term293 = term293.
Proof. exact (MK_COMB (@lem2290054) (@lem2290049)). Qed.
Lemma lem2290080 : term288 = term293.
Proof. exact (TRANS (@lem2290029) (@lem2290055)). Qed.
Lemma lem2290081 : term293 = term288.
Proof. exact (SYM (@lem2290080)). Qed.
Lemma lem2290083 (h1 : term99) : term99.
Proof. exact (h1). Qed.
Lemma lem2290089 (h1 : term287) : term287.
Proof. exact (h1). Qed.
Lemma lem2290093 (x : real) (n : nat) : (x = (real_of_num n)) = (x = (real_of_num n)).
Proof. exact (eq_refl (x = (real_of_num n))). Qed.
Lemma lem2290094 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem2290095 (x : real) : (term105 x) = (term106 x).
Proof. exact (@lem2290094 (term73 x)). Qed.
Lemma lem2290096 (x : real) (n : nat) : (term75 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term75 x n)). Qed.
Lemma lem2290097 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2290099 (x : real) (n : nat) : (term107 x n) = (term108 x n).
Proof. exact (MK_COMB (@lem2290097) (@lem2290096 x n)). Qed.
Lemma lem2290100 (x : real) : (term109 x) = (term110 x).
Proof. exact (fun_ext (fun n : nat => @lem2290099 x n)). Qed.
Lemma lem2290101 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2290102 (x : real) : (term106 x) = (term111 x).
Proof. exact (MK_COMB (@lem2290101) (@lem2290100 x)). Qed.
Lemma lem2290103 (x : real) : (term105 x) = (term111 x).
Proof. exact (TRANS (@lem2290095 x) (@lem2290102 x)). Qed.
Lemma lem2290104 (x : real) : (term73 x) = (term73 x).
Proof. exact (fun_ext (fun n : nat => @lem2290093 x n)). Qed.
Lemma lem2290105 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290106 (x : real) : (term89 x) = (term89 x).
Proof. exact (MK_COMB (@lem2290105) (@lem2290104 x)). Qed.
Lemma lem2290108 (x : real) (n : nat) : (x = (term79 n)) = (x = (term79 n)).
Proof. exact (eq_refl (x = (term79 n))). Qed.
Lemma lem2290109 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem2290110 (x : real) : (term112 x) = (term113 x).
Proof. exact (@lem2290109 (term74 x)). Qed.
Lemma lem2290111 (x : real) (n : nat) : (term78 x n) = (x = (term79 n)).
Proof. exact (eq_refl (term78 x n)). Qed.
Lemma lem2290112 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2290114 (x : real) (n : nat) : (term114 x n) = (term115 x n).
Proof. exact (MK_COMB (@lem2290112) (@lem2290111 x n)). Qed.
Lemma lem2290115 (x : real) : (term116 x) = (term117 x).
Proof. exact (fun_ext (fun n : nat => @lem2290114 x n)). Qed.
Lemma lem2290116 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2290117 (x : real) : (term113 x) = (term118 x).
Proof. exact (MK_COMB (@lem2290116) (@lem2290115 x)). Qed.
Lemma lem2290118 (x : real) : (term112 x) = (term118 x).
Proof. exact (TRANS (@lem2290110 x) (@lem2290117 x)). Qed.
Lemma lem2290119 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun n : nat => @lem2290108 x n)). Qed.
Lemma lem2290120 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290121 (x : real) : (term94 x) = (term94 x).
Proof. exact (MK_COMB (@lem2290120) (@lem2290119 x)). Qed.
Lemma lem2290122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2290123 (x : real) : (term119 x) = (term120 x).
Proof. exact (MK_COMB (@lem2290122) (@lem2290103 x)). Qed.
Lemma lem2290124 (x : real) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem2290123 x) (@lem2290118 x)). Qed.
Lemma lem2290125 (x : real) : (term123 x) = (term121 x).
Proof. exact (@lem17160 (term89 x) (term94 x)). Qed.
Lemma lem2290126 (x : real) : (term123 x) = (term122 x).
Proof. exact (TRANS (@lem2290125 x) (@lem2290124 x)). Qed.
Lemma lem2290127 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2290128 (x : real) : (term91 x) = (term91 x).
Proof. exact (MK_COMB (@lem2290127) (@lem2290106 x)). Qed.
Lemma lem2290129 (x : real) : (term95 x) = (term95 x).
Proof. exact (MK_COMB (@lem2290128 x) (@lem2290121 x)). Qed.
Lemma lem2290131 (x : real) : (term124 x) = (term124 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem2290132 (x : real) : (term125 x) = (term125 x).
Proof. exact (MK_COMB (@lem2290131 x) (@lem2290129 x)). Qed.
Lemma lem2290134 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem2290135 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem2290134 x) (@lem2290126 x)). Qed.
Lemma lem2290136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2290137 (x : real) : (term129 x) = (term130 x).
Proof. exact (MK_COMB (@lem2290136) (@lem2290135 x)). Qed.
Lemma lem2290138 (x : real) : (term131 x) = (term132 x).
Proof. exact (MK_COMB (@lem2290137 x) (@lem2290132 x)). Qed.
Lemma lem2290139 (x : real) : ((integer x) = (term95 x)) = (term131 x).
Proof. exact (@lem17784 (integer x) (term95 x)). Qed.
Lemma lem2290140 (x : real) : ((integer x) = (term95 x)) = (term132 x).
Proof. exact (TRANS (@lem2290139 x) (@lem2290138 x)). Qed.
Lemma lem2290141 : term98 = term133.
Proof. exact (fun_ext (fun x : real => @lem2290140 x)). Qed.
Lemma lem2290142 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290143 : term99 = term134.
Proof. exact (MK_COMB (@lem2290142) (@lem2290141)). Qed.
Lemma lem2290145 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem2290146 (P : real -> Prop) (Q : real -> Prop) : (term137 P Q) = (term138 P Q).
Proof. exact (@lem2290145 real P Q). Qed.
Lemma lem2290147 : term139 = term140.
Proof. exact (@lem2290146 term141 term142). Qed.
Lemma lem2290148 (x : real) : (term143 x) = (term128 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem2290149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2290150 (x : real) : (term144 x) = (term130 x).
Proof. exact (MK_COMB (@lem2290149) (@lem2290148 x)). Qed.
Lemma lem2290151 (x : real) : (term145 x) = (term125 x).
Proof. exact (eq_refl (term145 x)). Qed.
Lemma lem2290152 (x : real) : (term146 x) = (term132 x).
Proof. exact (MK_COMB (@lem2290150 x) (@lem2290151 x)). Qed.
Lemma lem2290153 : term147 = term133.
Proof. exact (fun_ext (fun x : real => @lem2290152 x)). Qed.
Lemma lem2290154 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290155 : term139 = term134.
Proof. exact (MK_COMB (@lem2290154) (@lem2290153)). Qed.
Lemma lem2290156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2290157 : term148 = term149.
Proof. exact (MK_COMB (@lem2290156) (@lem2290155)). Qed.
Lemma lem2290158 (x : real) : (term143 x) = (term128 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem2290159 : term150 = term141.
Proof. exact (fun_ext (fun x : real => @lem2290158 x)). Qed.
Lemma lem2290160 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290161 : term151 = term152.
Proof. exact (MK_COMB (@lem2290160) (@lem2290159)). Qed.
Lemma lem2290162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2290163 : term153 = term154.
Proof. exact (MK_COMB (@lem2290162) (@lem2290161)). Qed.
Lemma lem2290164 (x : real) : (term145 x) = (term125 x).
Proof. exact (eq_refl (term145 x)). Qed.
Lemma lem2290165 : term155 = term142.
Proof. exact (fun_ext (fun x : real => @lem2290164 x)). Qed.
Lemma lem2290166 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290167 : term156 = term157.
Proof. exact (MK_COMB (@lem2290166) (@lem2290165)). Qed.
Lemma lem2290168 : term140 = term158.
Proof. exact (MK_COMB (@lem2290163) (@lem2290167)). Qed.
Lemma lem2290169 : (term139 = term140) = (term134 = term158).
Proof. exact (MK_COMB (@lem2290157) (@lem2290168)). Qed.
Lemma lem2290170 : term134 = term158.
Proof. exact (EQ_MP (@lem2290169) (@lem2290147)). Qed.
Lemma lem2290264 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term68 A P Q) = (term67 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2290265 (P : nat -> Prop) (Q : nat -> Prop) : (term70 P Q) = (term69 P Q).
Proof. exact (@lem2290264 nat P Q). Qed.
Lemma lem2290266 (x : real) : (term72 x) = (term71 x).
Proof. exact (@lem2290265 (term73 x) (term74 x)). Qed.
Lemma lem2290267 (x : real) (n : nat) : (term75 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term75 x n)). Qed.
Lemma lem2290268 (x : real) : (term87 x) = (term73 x).
Proof. exact (fun_ext (fun n : nat => @lem2290267 x n)). Qed.
Lemma lem2290269 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290270 (x : real) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem2290269) (@lem2290268 x)). Qed.
Lemma lem2290271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2290272 (x : real) : (term90 x) = (term91 x).
Proof. exact (MK_COMB (@lem2290271) (@lem2290270 x)). Qed.
Lemma lem2290273 (x : real) (n : nat) : (term78 x n) = (x = (term79 n)).
Proof. exact (eq_refl (term78 x n)). Qed.
Lemma lem2290274 (x : real) : (term92 x) = (term74 x).
Proof. exact (fun_ext (fun n : nat => @lem2290273 x n)). Qed.
Lemma lem2290275 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290276 (x : real) : (term93 x) = (term94 x).
Proof. exact (MK_COMB (@lem2290275) (@lem2290274 x)). Qed.
Lemma lem2290277 (x : real) : (term72 x) = (term95 x).
Proof. exact (MK_COMB (@lem2290272 x) (@lem2290276 x)). Qed.
Lemma lem2290278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2290279 (x : real) : (term159 x) = (term160 x).
Proof. exact (MK_COMB (@lem2290278) (@lem2290277 x)). Qed.
Lemma lem2290280 (x : real) (n : nat) : (term75 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term75 x n)). Qed.
Lemma lem2290281 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2290282 (x : real) (n : nat) : (term76 x n) = (term77 x n).
Proof. exact (MK_COMB (@lem2290281) (@lem2290280 x n)). Qed.
Lemma lem2290283 (x : real) (n : nat) : (term78 x n) = (x = (term79 n)).
Proof. exact (eq_refl (term78 x n)). Qed.
Lemma lem2290284 (x : real) (n : nat) : (term80 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem2290282 x n) (@lem2290283 x n)). Qed.
Lemma lem2290285 (x : real) : (term82 x) = (term83 x).
Proof. exact (fun_ext (fun n : nat => @lem2290284 x n)). Qed.
Lemma lem2290286 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290287 (x : real) : (term71 x) = (term84 x).
Proof. exact (MK_COMB (@lem2290286) (@lem2290285 x)). Qed.
Lemma lem2290288 (x : real) : ((term72 x) = (term71 x)) = ((term95 x) = (term84 x)).
Proof. exact (MK_COMB (@lem2290279 x) (@lem2290287 x)). Qed.
Lemma lem2290289 (x : real) : (term95 x) = (term84 x).
Proof. exact (EQ_MP (@lem2290288 x) (@lem2290266 x)). Qed.
Lemma lem2290290 (x : real) : (term124 x) = (term124 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem2290291 (x : real) : (term125 x) = (term161 x).
Proof. exact (MK_COMB (@lem2290290 x) (@lem2290289 x)). Qed.
Lemma lem2290293 {A : Type'} (P : Prop) (Q : A -> Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem2290294 (P : Prop) (Q : nat -> Prop) : (term164 P Q) = (term165 P Q).
Proof. exact (@lem2290293 nat P Q). Qed.
Lemma lem2290295 (x : real) : (term166 x) = (term167 x).
Proof. exact (@lem2290294 (term168 x) (term83 x)). Qed.
Lemma lem2290296 (x : real) (n : nat) : (term169 x n) = (term81 x n).
Proof. exact (eq_refl (term169 x n)). Qed.
Lemma lem2290297 (x : real) : (term170 x) = (term83 x).
Proof. exact (fun_ext (fun n : nat => @lem2290296 x n)). Qed.
Lemma lem2290298 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290299 (x : real) : (term171 x) = (term84 x).
Proof. exact (MK_COMB (@lem2290298) (@lem2290297 x)). Qed.
Lemma lem2290300 (x : real) : (term124 x) = (term124 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem2290301 (x : real) : (term166 x) = (term161 x).
Proof. exact (MK_COMB (@lem2290300 x) (@lem2290299 x)). Qed.
Lemma lem2290302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2290303 (x : real) : (term172 x) = (term173 x).
Proof. exact (MK_COMB (@lem2290302) (@lem2290301 x)). Qed.
Lemma lem2290304 (x : real) (n : nat) : (term169 x n) = (term81 x n).
Proof. exact (eq_refl (term169 x n)). Qed.
Lemma lem2290305 (x : real) : (term124 x) = (term124 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem2290306 (x : real) (n : nat) : (term174 x n) = (term175 x n).
Proof. exact (MK_COMB (@lem2290305 x) (@lem2290304 x n)). Qed.
Lemma lem2290307 (x : real) : (term176 x) = (term177 x).
Proof. exact (fun_ext (fun n : nat => @lem2290306 x n)). Qed.
Lemma lem2290308 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290309 (x : real) : (term167 x) = (term178 x).
Proof. exact (MK_COMB (@lem2290308) (@lem2290307 x)). Qed.
Lemma lem2290310 (x : real) : ((term166 x) = (term167 x)) = ((term161 x) = (term178 x)).
Proof. exact (MK_COMB (@lem2290303 x) (@lem2290309 x)). Qed.
Lemma lem2290311 (x : real) : (term161 x) = (term178 x).
Proof. exact (EQ_MP (@lem2290310 x) (@lem2290295 x)). Qed.
Lemma lem2290312 (x : real) : (term125 x) = (term178 x).
Proof. exact (TRANS (@lem2290291 x) (@lem2290311 x)). Qed.
Lemma lem2290313 : term142 = term179.
Proof. exact (fun_ext (fun x : real => @lem2290312 x)). Qed.
Lemma lem2290314 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290315 : term157 = term180.
Proof. exact (MK_COMB (@lem2290314) (@lem2290313)). Qed.
Lemma lem2290317 {A B : Type'} (P : type1413 A B) : (term181 A B P) = (term182 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem2290318 (P : type1622) : (term183 P) = (term184 P).
Proof. exact (@lem2290317 real nat P). Qed.
Lemma lem2290319 : term185 = term186.
Proof. exact (@lem2290318 term187). Qed.
Lemma lem2290320 (x : real) : (term188 x) = (term177 x).
Proof. exact (eq_refl (term188 x)). Qed.
Lemma lem2290321 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2290322 (x : real) (n : nat) : (term189 x n) = (term190 x n).
Proof. exact (MK_COMB (@lem2290320 x) (@lem2290321 n)). Qed.
Lemma lem2290323 (x : real) (n : nat) : (term190 x n) = (term175 x n).
Proof. exact (eq_refl (term190 x n)). Qed.
Lemma lem2290324 (x : real) (n : nat) : (term189 x n) = (term175 x n).
Proof. exact (TRANS (@lem2290322 x n) (@lem2290323 x n)). Qed.
Lemma lem2290325 (x : real) : (term191 x) = (term177 x).
Proof. exact (fun_ext (fun n : nat => @lem2290324 x n)). Qed.
Lemma lem2290326 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290327 (x : real) : (term192 x) = (term178 x).
Proof. exact (MK_COMB (@lem2290326) (@lem2290325 x)). Qed.
Lemma lem2290328 : term193 = term179.
Proof. exact (fun_ext (fun x : real => @lem2290327 x)). Qed.
Lemma lem2290329 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290330 : term185 = term180.
Proof. exact (MK_COMB (@lem2290329) (@lem2290328)). Qed.
Lemma lem2290331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2290332 : term194 = term195.
Proof. exact (MK_COMB (@lem2290331) (@lem2290330)). Qed.
Lemma lem2290333 (x : real) : (term188 x) = (term177 x).
Proof. exact (eq_refl (term188 x)). Qed.
Lemma lem2290334 (n : real -> nat) (x : real) : (n x) = (n x).
Proof. exact (eq_refl (n x)). Qed.
Lemma lem2290335 (n : real -> nat) (x : real) : (term196 n x) = (term197 n x).
Proof. exact (MK_COMB (@lem2290333 x) (@lem2290334 n x)). Qed.
Lemma lem2290336 (n : real -> nat) (x : real) : (term197 n x) = (term198 n x).
Proof. exact (eq_refl (term197 n x)). Qed.
Lemma lem2290337 (n : real -> nat) (x : real) : (term196 n x) = (term198 n x).
Proof. exact (TRANS (@lem2290335 n x) (@lem2290336 n x)). Qed.
Lemma lem2290338 (n : real -> nat) : (term199 n) = (term200 n).
Proof. exact (fun_ext (fun x : real => @lem2290337 n x)). Qed.
Lemma lem2290339 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290340 (n : real -> nat) : (term201 n) = (term202 n).
Proof. exact (MK_COMB (@lem2290339) (@lem2290338 n)). Qed.
Lemma lem2290341 : term203 = term204.
Proof. exact (fun_ext (fun n : real -> nat => @lem2290340 n)). Qed.
Lemma lem2290342 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem2290343 : term186 = term205.
Proof. exact (MK_COMB (@lem2290342) (@lem2290341)). Qed.
Lemma lem2290344 : (term185 = term186) = (term180 = term205).
Proof. exact (MK_COMB (@lem2290332) (@lem2290343)). Qed.
Lemma lem2290345 : term180 = term205.
Proof. exact (EQ_MP (@lem2290344) (@lem2290319)). Qed.
Lemma lem2290346 : term157 = term205.
Proof. exact (TRANS (@lem2290315) (@lem2290345)). Qed.
Lemma lem2290347 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem2290348 : term158 = term206.
Proof. exact (MK_COMB (@lem2290347) (@lem2290346)). Qed.
Lemma lem2290350 {A : Type'} (P : Prop) (Q : A -> Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem2290351 (P : Prop) (Q : type1024) : (term209 P Q) = (term210 P Q).
Proof. exact (@lem2290350 (real -> nat) P Q). Qed.
Lemma lem2290352 : term211 = term212.
Proof. exact (@lem2290351 term152 term204). Qed.
Lemma lem2290353 (n : real -> nat) : (term213 n) = (term202 n).
Proof. exact (eq_refl (term213 n)). Qed.
Lemma lem2290354 : term214 = term204.
Proof. exact (fun_ext (fun n : real -> nat => @lem2290353 n)). Qed.
Lemma lem2290355 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem2290356 : term215 = term205.
Proof. exact (MK_COMB (@lem2290355) (@lem2290354)). Qed.
Lemma lem2290357 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem2290358 : term211 = term206.
Proof. exact (MK_COMB (@lem2290357) (@lem2290356)). Qed.
Lemma lem2290359 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2290360 : term216 = term217.
Proof. exact (MK_COMB (@lem2290359) (@lem2290358)). Qed.
Lemma lem2290361 (n : real -> nat) : (term213 n) = (term202 n).
Proof. exact (eq_refl (term213 n)). Qed.
Lemma lem2290362 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem2290363 (n : real -> nat) : (term218 n) = (term219 n).
Proof. exact (MK_COMB (@lem2290362) (@lem2290361 n)). Qed.
Lemma lem2290364 : term220 = term221.
Proof. exact (fun_ext (fun n : real -> nat => @lem2290363 n)). Qed.
Lemma lem2290365 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem2290366 : term212 = term222.
Proof. exact (MK_COMB (@lem2290365) (@lem2290364)). Qed.
Lemma lem2290367 : (term211 = term212) = (term206 = term222).
Proof. exact (MK_COMB (@lem2290360) (@lem2290366)). Qed.
Lemma lem2290368 : term206 = term222.
Proof. exact (EQ_MP (@lem2290367) (@lem2290352)). Qed.
Lemma lem2290369 : term158 = term222.
Proof. exact (TRANS (@lem2290348) (@lem2290368)). Qed.
Lemma lem2290370 : term134 = term222.
Proof. exact (TRANS (@lem2290170) (@lem2290369)). Qed.
Lemma lem2290371 : term99 = term222.
Proof. exact (TRANS (@lem2290143) (@lem2290370)). Qed.
Lemma lem2290372 (h1 : term99) : term222.
Proof. exact (EQ_MP (@lem2290371) (@lem2290083 h1)). Qed.
Lemma lem2290373 (n : real -> nat) (h1 : term219 n) : term219 n.
Proof. exact (h1). Qed.
Lemma lem2290387 (h1 : term287) : term287.
Proof. exact (h1). Qed.
Lemma lem2290418 (n : real -> nat) (x : real) : (term198 n x) = (term198 n x).
Proof. exact (eq_refl (term198 n x)). Qed.
Lemma lem2290419 (n : real -> nat) : (term200 n) = (term200 n).
Proof. exact (fun_ext (fun x : real => @lem2290418 n x)). Qed.
Lemma lem2290420 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290421 (n : real -> nat) : (term202 n) = (term202 n).
Proof. exact (MK_COMB (@lem2290420) (@lem2290419 n)). Qed.
Lemma lem2290432 (x : real) (n : nat) : (term115 x n) = (term115 x n).
Proof. exact (eq_refl (term115 x n)). Qed.
Lemma lem2290433 (x : real) : (term117 x) = (term117 x).
Proof. exact (fun_ext (fun n : nat => @lem2290432 x n)). Qed.
Lemma lem2290434 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2290435 (x : real) : (term118 x) = (term118 x).
Proof. exact (MK_COMB (@lem2290434) (@lem2290433 x)). Qed.
Lemma lem2290444 (x : real) (n : nat) : (term108 x n) = (term108 x n).
Proof. exact (eq_refl (term108 x n)). Qed.
Lemma lem2290445 (x : real) : (term110 x) = (term110 x).
Proof. exact (fun_ext (fun n : nat => @lem2290444 x n)). Qed.
Lemma lem2290446 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2290447 (x : real) : (term111 x) = (term111 x).
Proof. exact (MK_COMB (@lem2290446) (@lem2290445 x)). Qed.
Lemma lem2290448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2290449 (x : real) : (term120 x) = (term120 x).
Proof. exact (MK_COMB (@lem2290448) (@lem2290447 x)). Qed.
Lemma lem2290450 (x : real) : (term122 x) = (term122 x).
Proof. exact (MK_COMB (@lem2290449 x) (@lem2290435 x)). Qed.
Lemma lem2290455 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem2290456 (x : real) : (term128 x) = (term128 x).
Proof. exact (MK_COMB (@lem2290455 x) (@lem2290450 x)). Qed.
Lemma lem2290457 : term141 = term141.
Proof. exact (fun_ext (fun x : real => @lem2290456 x)). Qed.
Lemma lem2290458 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290459 : term152 = term152.
Proof. exact (MK_COMB (@lem2290458) (@lem2290457)). Qed.
Lemma lem2290460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2290461 : term154 = term154.
Proof. exact (MK_COMB (@lem2290460) (@lem2290459)). Qed.
Lemma lem2290462 (n : real -> nat) : (term219 n) = (term219 n).
Proof. exact (MK_COMB (@lem2290461) (@lem2290421 n)). Qed.
Lemma lem2290463 (n : real -> nat) (h1 : term219 n) : term219 n.
Proof. exact (EQ_MP (@lem2290462 n) (@lem2290373 n h1)). Qed.
Lemma lem2290465 (n : real -> nat) (h1 : term219 n) : term152.
Proof. exact (proj1 (@lem2290463 n h1)). Qed.
Lemma lem2290469 (h1 : term287) : term287.
Proof. exact (h1). Qed.
Lemma lem2290471 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem2290472 (P : nat -> Prop) (Q : nat -> Prop) : (term223 P Q) = (term224 P Q).
Proof. exact (@lem2290471 nat P Q). Qed.
Lemma lem2290473 (x : real) : (term225 x) = (term226 x).
Proof. exact (@lem2290472 (term110 x) (term117 x)). Qed.
Lemma lem2290474 (x : real) (n : nat) : (term227 x n) = (term108 x n).
Proof. exact (eq_refl (term227 x n)). Qed.
Lemma lem2290475 (x : real) : (term228 x) = (term110 x).
Proof. exact (fun_ext (fun n : nat => @lem2290474 x n)). Qed.
Lemma lem2290476 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2290477 (x : real) : (term229 x) = (term111 x).
Proof. exact (MK_COMB (@lem2290476) (@lem2290475 x)). Qed.
Lemma lem2290478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2290479 (x : real) : (term230 x) = (term120 x).
Proof. exact (MK_COMB (@lem2290478) (@lem2290477 x)). Qed.
Lemma lem2290480 (x : real) (n : nat) : (term231 x n) = (term115 x n).
Proof. exact (eq_refl (term231 x n)). Qed.
Lemma lem2290481 (x : real) : (term232 x) = (term117 x).
Proof. exact (fun_ext (fun n : nat => @lem2290480 x n)). Qed.
Lemma lem2290482 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2290483 (x : real) : (term233 x) = (term118 x).
Proof. exact (MK_COMB (@lem2290482) (@lem2290481 x)). Qed.
Lemma lem2290484 (x : real) : (term225 x) = (term122 x).
Proof. exact (MK_COMB (@lem2290479 x) (@lem2290483 x)). Qed.
Lemma lem2290485 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2290486 (x : real) : (term234 x) = (term235 x).
Proof. exact (MK_COMB (@lem2290485) (@lem2290484 x)). Qed.
Lemma lem2290487 (x : real) (n : nat) : (term227 x n) = (term108 x n).
Proof. exact (eq_refl (term227 x n)). Qed.
Lemma lem2290488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2290489 (x : real) (n : nat) : (term236 x n) = (term237 x n).
Proof. exact (MK_COMB (@lem2290488) (@lem2290487 x n)). Qed.
Lemma lem2290490 (x : real) (n : nat) : (term231 x n) = (term115 x n).
Proof. exact (eq_refl (term231 x n)). Qed.
Lemma lem2290491 (x : real) (n : nat) : (term238 x n) = (term239 x n).
Proof. exact (MK_COMB (@lem2290489 x n) (@lem2290490 x n)). Qed.
Lemma lem2290492 (x : real) : (term240 x) = (term241 x).
Proof. exact (fun_ext (fun n : nat => @lem2290491 x n)). Qed.
Lemma lem2290493 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2290494 (x : real) : (term226 x) = (term242 x).
Proof. exact (MK_COMB (@lem2290493) (@lem2290492 x)). Qed.
Lemma lem2290495 (x : real) : ((term225 x) = (term226 x)) = ((term122 x) = (term242 x)).
Proof. exact (MK_COMB (@lem2290486 x) (@lem2290494 x)). Qed.
Lemma lem2290496 (x : real) : (term122 x) = (term242 x).
Proof. exact (EQ_MP (@lem2290495 x) (@lem2290473 x)). Qed.
Lemma lem2290497 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem2290498 (x : real) : (term128 x) = (term243 x).
Proof. exact (MK_COMB (@lem2290497 x) (@lem2290496 x)). Qed.
Lemma lem2290500 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem2290501 (P : Prop) (Q : nat -> Prop) : (term246 P Q) = (term247 P Q).
Proof. exact (@lem2290500 nat P Q). Qed.
Lemma lem2290502 (x : real) : (term248 x) = (term249 x).
Proof. exact (@lem2290501 (integer x) (term241 x)). Qed.
Lemma lem2290503 (x : real) (n : nat) : (term250 x n) = (term239 x n).
Proof. exact (eq_refl (term250 x n)). Qed.
Lemma lem2290504 (x : real) : (term251 x) = (term241 x).
Proof. exact (fun_ext (fun n : nat => @lem2290503 x n)). Qed.
Lemma lem2290505 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2290506 (x : real) : (term252 x) = (term242 x).
Proof. exact (MK_COMB (@lem2290505) (@lem2290504 x)). Qed.
Lemma lem2290507 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem2290508 (x : real) : (term248 x) = (term243 x).
Proof. exact (MK_COMB (@lem2290507 x) (@lem2290506 x)). Qed.
Lemma lem2290509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2290510 (x : real) : (term253 x) = (term254 x).
Proof. exact (MK_COMB (@lem2290509) (@lem2290508 x)). Qed.
Lemma lem2290511 (x : real) (n : nat) : (term250 x n) = (term239 x n).
Proof. exact (eq_refl (term250 x n)). Qed.
Lemma lem2290512 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem2290513 (x : real) (n : nat) : (term255 x n) = (term256 x n).
Proof. exact (MK_COMB (@lem2290512 x) (@lem2290511 x n)). Qed.
Lemma lem2290514 (x : real) : (term257 x) = (term258 x).
Proof. exact (fun_ext (fun n : nat => @lem2290513 x n)). Qed.
Lemma lem2290515 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2290516 (x : real) : (term249 x) = (term259 x).
Proof. exact (MK_COMB (@lem2290515) (@lem2290514 x)). Qed.
Lemma lem2290517 (x : real) : ((term248 x) = (term249 x)) = ((term243 x) = (term259 x)).
Proof. exact (MK_COMB (@lem2290510 x) (@lem2290516 x)). Qed.
Lemma lem2290518 (x : real) : (term243 x) = (term259 x).
Proof. exact (EQ_MP (@lem2290517 x) (@lem2290502 x)). Qed.
Lemma lem2290519 (x : real) : (term128 x) = (term259 x).
Proof. exact (TRANS (@lem2290498 x) (@lem2290518 x)). Qed.
Lemma lem2290520 : term141 = term260.
Proof. exact (fun_ext (fun x : real => @lem2290519 x)). Qed.
Lemma lem2290521 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290522 : term152 = term261.
Proof. exact (MK_COMB (@lem2290521) (@lem2290520)). Qed.
Lemma lem2290539 (x : real) (n : nat) : (term256 x n) = (term262 x n).
Proof. exact (@lem19490 (term108 x n) (integer x) (term115 x n)). Qed.
Lemma lem2290540 (x : real) : (term258 x) = (term263 x).
Proof. exact (fun_ext (fun n : nat => @lem2290539 x n)). Qed.
Lemma lem2290541 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2290542 (x : real) : (term259 x) = (term264 x).
Proof. exact (MK_COMB (@lem2290541) (@lem2290540 x)). Qed.
Lemma lem2290543 : term260 = term265.
Proof. exact (fun_ext (fun x : real => @lem2290542 x)). Qed.
Lemma lem2290544 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290545 : term261 = term266.
Proof. exact (MK_COMB (@lem2290544) (@lem2290543)). Qed.
Lemma lem2290546 : term152 = term266.
Proof. exact (TRANS (@lem2290522) (@lem2290545)). Qed.
Lemma lem2290547 (n : real -> nat) (h1 : term219 n) : term266.
Proof. exact (EQ_MP (@lem2290546) (@lem2290465 n h1)). Qed.
Lemma lem2290567 (_28783 : real) (n : real -> nat) (h1 : term219 n) : term267 _28783.
Proof. exact (@lem2290547 n h1 _28783). Qed.
Lemma lem2290568 (_28783 : real) : (term267 _28783) = (term264 _28783).
Proof. exact (eq_refl (term267 _28783)). Qed.
Lemma lem2290569 (_28783 : real) (n : real -> nat) (h1 : term219 n) : term264 _28783.
Proof. exact (EQ_MP (@lem2290568 _28783) (@lem2290567 _28783 n h1)). Qed.
Lemma lem2290570 (_28783 : real) (_28784 : nat) (n : real -> nat) (h1 : term219 n) : term268 _28783 _28784.
Proof. exact (@lem2290569 _28783 n h1 _28784). Qed.
Lemma lem2290571 (_28783 : real) (_28784 : nat) : (term268 _28783 _28784) = (term262 _28783 _28784).
Proof. exact (eq_refl (term268 _28783 _28784)). Qed.
Lemma lem2290572 (_28783 : real) (_28784 : nat) (n : real -> nat) (h1 : term219 n) : term262 _28783 _28784.
Proof. exact (EQ_MP (@lem2290571 _28783 _28784) (@lem2290570 _28783 _28784 n h1)). Qed.
Lemma lem2290579 (h1 : term287) : term287.
Proof. exact (h1). Qed.
Lemma lem2290601 (_28783 : real) (_28784 : nat) (n : real -> nat) (h1 : term219 n) : term294 _28783 _28784.
Proof. exact (proj2 (@lem2290572 _28783 _28784 n h1)). Qed.
Lemma lem2290659 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem2290660 : term40 = term40.
Proof. exact (@lem2290659 term40). Qed.
Lemma lem2290661 : term295.
Proof. exact (fun h0 : term296 => @lem2290660). Qed.
Lemma lem2290663 (p : Prop) : (term272 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2290664 : term295 = (term40 = term40).
Proof. exact (@lem2290663 (term40 = term40)). Qed.
Lemma lem2290665 : term40 = term40.
Proof. exact (EQ_MP (@lem2290664) (@lem2290661)). Qed.
Lemma lem2290667 (b : Prop) (a : Prop) : (a \/ b) = (term273 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2290668 (_28784 : nat) (_28783 : real) : (term294 _28783 _28784) = (term297 _28784 _28783).
Proof. exact (@lem2290667 (term115 _28783 _28784) (integer _28783)). Qed.
Lemma lem2290670 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2290671 (_28783 : real) (_28784 : nat) : (term298 _28783 _28784) = (_28783 = (term79 _28784)).
Proof. exact (@lem2290670 (_28783 = (term79 _28784))). Qed.
Lemma lem2290672 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2290673 (_28783 : real) (_28784 : nat) : (term299 _28783 _28784) = (term300 _28783 _28784).
Proof. exact (MK_COMB (@lem2290672) (@lem2290671 _28783 _28784)). Qed.
Lemma lem2290674 (_28783 : real) : (integer _28783) = (integer _28783).
Proof. exact (eq_refl (integer _28783)). Qed.
Lemma lem2290675 (_28784 : nat) (_28783 : real) : (term297 _28784 _28783) = (term301 _28784 _28783).
Proof. exact (MK_COMB (@lem2290673 _28783 _28784) (@lem2290674 _28783)). Qed.
Lemma lem2290676 (_28784 : nat) (_28783 : real) : (term294 _28783 _28784) = (term301 _28784 _28783).
Proof. exact (TRANS (@lem2290668 _28784 _28783) (@lem2290675 _28784 _28783)). Qed.
Lemma lem2290679 (_28784 : nat) (_28783 : real) (n : real -> nat) (h1 : term219 n) : term301 _28784 _28783.
Proof. exact (EQ_MP (@lem2290676 _28784 _28783) (@lem2290601 _28783 _28784 n h1)). Qed.
Lemma lem2290680 (n : real -> nat) (h1 : term219 n) : term302.
Proof. exact (@lem2290679 term281 term40 n h1). Qed.
Lemma lem2290683 (n : real -> nat) (h1 : term219 n) : term49.
Proof. exact (@lem2290680 n h1 (@lem2290665)). Qed.
Lemma lem2290684 (n : real -> nat) (h1 : term219 n) : term303.
Proof. exact (fun h0 : term287 => @lem2290683 n h1). Qed.
Lemma lem2290686 (p : Prop) : (term272 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2290687 : term303 = term49.
Proof. exact (@lem2290686 term49). Qed.
Lemma lem2290688 (n : real -> nat) (h1 : term219 n) : term49.
Proof. exact (EQ_MP (@lem2290687) (@lem2290684 n h1)). Qed.
Lemma lem2290691 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2290693 : term287 = term304.
Proof. exact (@lem2290691 term49). Qed.
Lemma lem2290696 (h1 : term287) : term304.
Proof. exact (EQ_MP (@lem2290693) (@lem2290579 h1)). Qed.
Lemma lem2290699 (n : real -> nat) (h1 : term287) (h2 : term219 n) : False.
Proof. exact (@lem2290696 h1 (@lem2290688 n h2)). Qed.
Lemma lem2290700 (n : real -> nat) (h1 : term287) (h2 : term219 n) : term284.
Proof. exact (fun h0 : ~ False => @lem2290699 n h1 h2). Qed.
Lemma lem2290702 (p : Prop) : (term272 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2290703 : term284 = False.
Proof. exact (@lem2290702 False). Qed.
Lemma lem2290704 (n : real -> nat) (h1 : term287) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2290703) (@lem2290700 n h1 h2)). Qed.
Lemma lem2290705 (n : real -> nat) (h1 : term287) (h2 : term219 n) : term287 = False.
Proof. exact (prop_ext (fun h3 : term287 => @lem2290704 n h1 h2) (fun h3 : False => @lem2290579 h1)). Qed.
Lemma lem2290706 (n : real -> nat) (h1 : term287) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2290705 n h1 h2) (@lem2290579 h1)). Qed.
Lemma lem2290707 (n : real -> nat) (h1 : term287) (h2 : term219 n) : term287 = False.
Proof. exact (prop_ext (fun h3 : term287 => @lem2290706 n h1 h2) (fun h3 : False => @lem2290469 h1)). Qed.
Lemma lem2290708 (n : real -> nat) (h1 : term287) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2290707 n h1 h2) (@lem2290469 h1)). Qed.
Lemma lem2290709 (n : real -> nat) (h1 : term287) (h2 : term219 n) : term287 = False.
Proof. exact (prop_ext (fun h3 : term287 => @lem2290708 n h1 h2) (fun h3 : False => @lem2290469 h1)). Qed.
Lemma lem2290710 (n : real -> nat) (h1 : term287) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2290709 n h1 h2) (@lem2290469 h1)). Qed.
Lemma lem2290711 (n : real -> nat) (h1 : term287) (h2 : term219 n) : (term219 n) = False.
Proof. exact (prop_ext (fun h3 : term219 n => @lem2290710 n h1 h2) (fun h3 : False => @lem2290463 n h2)). Qed.
Lemma lem2290712 (n : real -> nat) (h1 : term287) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2290711 n h1 h2) (@lem2290463 n h2)). Qed.
Lemma lem2290713 (n : real -> nat) (h1 : term287) (h2 : term219 n) : term287 = False.
Proof. exact (prop_ext (fun h3 : term287 => @lem2290712 n h1 h2) (fun h3 : False => @lem2290387 h1)). Qed.
Lemma lem2290714 (n : real -> nat) (h1 : term287) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2290713 n h1 h2) (@lem2290387 h1)). Qed.
Lemma lem2290715 (h1 : term99) (h2 : term287) : False.
Proof. exact (ex_elim (@lem2290372 h1) (fun n : real -> nat => fun h0 : term221 n => @lem2290714 n h2 h0)). Qed.
Lemma lem2290716 (h1 : term99) (h2 : term287) : term287 = False.
Proof. exact (prop_ext (fun h3 : term287 => @lem2290715 h1 h2) (fun h3 : False => @lem2290089 h2)). Qed.
Lemma lem2290717 (h1 : term99) (h2 : term287) : False.
Proof. exact (EQ_MP (@lem2290716 h1 h2) (@lem2290089 h2)). Qed.
Lemma lem2290718 (h1 : term287) : term285.
Proof. exact (fun h0 : term99 => @lem2290717 h0 h1). Qed.
Lemma lem2290719 : term285 = term100.
Proof. exact (@lem69 term99). Qed.
Lemma lem2290720 (h1 : term287) : term100.
Proof. exact (EQ_MP (@lem2290719) (@lem2290718 h1)). Qed.
Lemma lem2290721 : term293.
Proof. exact (fun h0 : term287 => @lem2290720 h0). Qed.
Lemma lem2290722 : term288.
Proof. exact (EQ_MP (@lem2290081) (@lem2290721)). Qed.
Lemma lem2290724 : term288.
Proof. exact (@lem2289963 (@lem2290722)). Qed.
Lemma lem2290725 (h1 : term287) : term65.
Proof. exact (@lem2290724 (@lem2289948 h1)). Qed.
Lemma lem2290726 (h1 : term287) : False.
Proof. exact (@lem2290725 h1 (@lem2288999)). Qed.
Lemma lem2290727 (h1 : term287) : term287 = False.
Proof. exact (prop_ext (fun h2 : term287 => @lem2290726 h1) (fun h2 : False => @lem2289948 h1)). Qed.
Lemma lem2290728 (h1 : term287) : False.
Proof. exact (EQ_MP (@lem2290727 h1) (@lem2289948 h1)). Qed.
Lemma lem2290729 : term286.
Proof. exact (fun h0 : term287 => @lem2290728 h0). Qed.
Lemma lem2290732 (p : Prop) : p = (term58 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2290733 : term44 = term305.
Proof. exact (@lem2290732 term44). Qed.
Lemma lem2290734 : term305 = term44.
Proof. exact (SYM (@lem2290733)). Qed.
Lemma lem2290735 (h1 : term306) : term306.
Proof. exact (h1). Qed.
Lemma lem2290738 (h1 : term307) : term307.
Proof. exact (h1). Qed.
Lemma lem2290739 : term308.
Proof. exact (fun h0 : term307 => @lem2290738 h0). Qed.
Lemma lem2290740 (h1 : term308) : term308.
Proof. exact (h1). Qed.
Lemma lem2290741 (h1 : term307) : term307.
Proof. exact (h1). Qed.
Lemma lem2290742 (h1 : term307) (h2 : term308) : term307.
Proof. exact (@lem2290740 h2 (@lem2290741 h1)). Qed.
Lemma lem2290743 (h1 : term307) : term309.
Proof. exact (fun h0 : term308 => @lem2290742 h1 h0). Qed.
Lemma lem2290744 (h1 : term308) : term308.
Proof. exact (h1). Qed.
Lemma lem2290745 (h1 : term307) (h2 : term308) : term307.
Proof. exact (@lem2290743 h1 (@lem2290744 h2)). Qed.
Lemma lem2290746 (h1 : term308) : term308.
Proof. exact (fun h0 : term307 => @lem2290745 h0 h1). Qed.
Lemma lem2290747 : term310.
Proof. exact (fun h0 : term308 => @lem2290746 h0). Qed.
Lemma lem2290750 : term308.
Proof. exact (@lem2290747 (@lem2290739)). Qed.
Lemma lem2290754 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2290755 : term65 = term66.
Proof. exact (@lem2290754 term0). Qed.
Lemma lem2290761 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term67 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2290762 (P : nat -> Prop) (Q : nat -> Prop) : (term69 P Q) = (term70 P Q).
Proof. exact (@lem2290761 nat P Q). Qed.
Lemma lem2290763 (x : real) : (term71 x) = (term72 x).
Proof. exact (@lem2290762 (term73 x) (term74 x)). Qed.
Lemma lem2290764 (x : real) (n : nat) : (term75 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term75 x n)). Qed.
Lemma lem2290765 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2290766 (x : real) (n : nat) : (term76 x n) = (term77 x n).
Proof. exact (MK_COMB (@lem2290765) (@lem2290764 x n)). Qed.
Lemma lem2290767 (x : real) (n : nat) : (term78 x n) = (x = (term79 n)).
Proof. exact (eq_refl (term78 x n)). Qed.
Lemma lem2290768 (x : real) (n : nat) : (term80 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem2290766 x n) (@lem2290767 x n)). Qed.
Lemma lem2290769 (x : real) : (term82 x) = (term83 x).
Proof. exact (fun_ext (fun n : nat => @lem2290768 x n)). Qed.
Lemma lem2290770 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290771 (x : real) : (term71 x) = (term84 x).
Proof. exact (MK_COMB (@lem2290770) (@lem2290769 x)). Qed.
Lemma lem2290772 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2290773 (x : real) : (term85 x) = (term86 x).
Proof. exact (MK_COMB (@lem2290772) (@lem2290771 x)). Qed.
Lemma lem2290774 (x : real) (n : nat) : (term75 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term75 x n)). Qed.
Lemma lem2290775 (x : real) : (term87 x) = (term73 x).
Proof. exact (fun_ext (fun n : nat => @lem2290774 x n)). Qed.
Lemma lem2290776 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290777 (x : real) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem2290776) (@lem2290775 x)). Qed.
Lemma lem2290778 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2290779 (x : real) : (term90 x) = (term91 x).
Proof. exact (MK_COMB (@lem2290778) (@lem2290777 x)). Qed.
Lemma lem2290780 (x : real) (n : nat) : (term78 x n) = (x = (term79 n)).
Proof. exact (eq_refl (term78 x n)). Qed.
Lemma lem2290781 (x : real) : (term92 x) = (term74 x).
Proof. exact (fun_ext (fun n : nat => @lem2290780 x n)). Qed.
Lemma lem2290782 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290783 (x : real) : (term93 x) = (term94 x).
Proof. exact (MK_COMB (@lem2290782) (@lem2290781 x)). Qed.
Lemma lem2290784 (x : real) : (term72 x) = (term95 x).
Proof. exact (MK_COMB (@lem2290779 x) (@lem2290783 x)). Qed.
Lemma lem2290785 (x : real) : ((term71 x) = (term72 x)) = ((term84 x) = (term95 x)).
Proof. exact (MK_COMB (@lem2290773 x) (@lem2290784 x)). Qed.
Lemma lem2290786 (x : real) : (term84 x) = (term95 x).
Proof. exact (EQ_MP (@lem2290785 x) (@lem2290763 x)). Qed.
Lemma lem2290797 (x : real) : (term96 x) = (term96 x).
Proof. exact (eq_refl (term96 x)). Qed.
Lemma lem2290798 (x : real) : ((integer x) = (term84 x)) = ((integer x) = (term95 x)).
Proof. exact (MK_COMB (@lem2290797 x) (@lem2290786 x)). Qed.
Lemma lem2290799 : term97 = term98.
Proof. exact (fun_ext (fun x : real => @lem2290798 x)). Qed.
Lemma lem2290800 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290801 : term0 = term99.
Proof. exact (MK_COMB (@lem2290800) (@lem2290799)). Qed.
Lemma lem2290806 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2290807 : term66 = term100.
Proof. exact (MK_COMB (@lem2290806) (@lem2290801)). Qed.
Lemma lem2290808 : term65 = term100.
Proof. exact (TRANS (@lem2290755) (@lem2290807)). Qed.
Lemma lem2290809 : term311 = term311.
Proof. exact (eq_refl term311). Qed.
Lemma lem2290816 : term307 = term312.
Proof. exact (MK_COMB (@lem2290809) (@lem2290808)). Qed.
Lemma lem2290817 (x : real) (n : nat) : (x = (term79 n)) = (x = (term79 n)).
Proof. exact (eq_refl (x = (term79 n))). Qed.
Lemma lem2290818 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun n : nat => @lem2290817 x n)). Qed.
Lemma lem2290819 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290820 (x : real) : (term94 x) = (term94 x).
Proof. exact (MK_COMB (@lem2290819) (@lem2290818 x)). Qed.
Lemma lem2290821 (x : real) (n : nat) : (x = (real_of_num n)) = (x = (real_of_num n)).
Proof. exact (eq_refl (x = (real_of_num n))). Qed.
Lemma lem2290822 (x : real) : (term73 x) = (term73 x).
Proof. exact (fun_ext (fun n : nat => @lem2290821 x n)). Qed.
Lemma lem2290823 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290824 (x : real) : (term89 x) = (term89 x).
Proof. exact (MK_COMB (@lem2290823) (@lem2290822 x)). Qed.
Lemma lem2290825 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2290826 (x : real) : (term91 x) = (term91 x).
Proof. exact (MK_COMB (@lem2290825) (@lem2290824 x)). Qed.
Lemma lem2290827 (x : real) : (term95 x) = (term95 x).
Proof. exact (MK_COMB (@lem2290826 x) (@lem2290820 x)). Qed.
Lemma lem2290830 (x : real) : (term96 x) = (term96 x).
Proof. exact (eq_refl (term96 x)). Qed.
Lemma lem2290831 (x : real) : ((integer x) = (term95 x)) = ((integer x) = (term95 x)).
Proof. exact (MK_COMB (@lem2290830 x) (@lem2290827 x)). Qed.
Lemma lem2290832 : term98 = term98.
Proof. exact (fun_ext (fun x : real => @lem2290831 x)). Qed.
Lemma lem2290833 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290834 : term99 = term99.
Proof. exact (MK_COMB (@lem2290833) (@lem2290832)). Qed.
Lemma lem2290835 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2290836 : term100 = term100.
Proof. exact (MK_COMB (@lem2290835) (@lem2290834)). Qed.
Lemma lem2290841 : term311 = term311.
Proof. exact (eq_refl term311). Qed.
Lemma lem2290842 : term312 = term312.
Proof. exact (MK_COMB (@lem2290841) (@lem2290836)). Qed.
Lemma lem2290867 : term307 = term312.
Proof. exact (TRANS (@lem2290816) (@lem2290842)). Qed.
Lemma lem2290868 : term312 = term307.
Proof. exact (SYM (@lem2290867)). Qed.
Lemma lem2290870 (h1 : term99) : term99.
Proof. exact (h1). Qed.
Lemma lem2290876 (h1 : term306) : term306.
Proof. exact (h1). Qed.
Lemma lem2290880 (x : real) (n : nat) : (x = (real_of_num n)) = (x = (real_of_num n)).
Proof. exact (eq_refl (x = (real_of_num n))). Qed.
Lemma lem2290881 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem2290882 (x : real) : (term105 x) = (term106 x).
Proof. exact (@lem2290881 (term73 x)). Qed.
Lemma lem2290883 (x : real) (n : nat) : (term75 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term75 x n)). Qed.
Lemma lem2290884 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2290886 (x : real) (n : nat) : (term107 x n) = (term108 x n).
Proof. exact (MK_COMB (@lem2290884) (@lem2290883 x n)). Qed.
Lemma lem2290887 (x : real) : (term109 x) = (term110 x).
Proof. exact (fun_ext (fun n : nat => @lem2290886 x n)). Qed.
Lemma lem2290888 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2290889 (x : real) : (term106 x) = (term111 x).
Proof. exact (MK_COMB (@lem2290888) (@lem2290887 x)). Qed.
Lemma lem2290890 (x : real) : (term105 x) = (term111 x).
Proof. exact (TRANS (@lem2290882 x) (@lem2290889 x)). Qed.
Lemma lem2290891 (x : real) : (term73 x) = (term73 x).
Proof. exact (fun_ext (fun n : nat => @lem2290880 x n)). Qed.
Lemma lem2290892 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290893 (x : real) : (term89 x) = (term89 x).
Proof. exact (MK_COMB (@lem2290892) (@lem2290891 x)). Qed.
Lemma lem2290895 (x : real) (n : nat) : (x = (term79 n)) = (x = (term79 n)).
Proof. exact (eq_refl (x = (term79 n))). Qed.
Lemma lem2290896 (P : nat -> Prop) : (term103 P) = (term104 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem2290897 (x : real) : (term112 x) = (term113 x).
Proof. exact (@lem2290896 (term74 x)). Qed.
Lemma lem2290898 (x : real) (n : nat) : (term78 x n) = (x = (term79 n)).
Proof. exact (eq_refl (term78 x n)). Qed.
Lemma lem2290899 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2290901 (x : real) (n : nat) : (term114 x n) = (term115 x n).
Proof. exact (MK_COMB (@lem2290899) (@lem2290898 x n)). Qed.
Lemma lem2290902 (x : real) : (term116 x) = (term117 x).
Proof. exact (fun_ext (fun n : nat => @lem2290901 x n)). Qed.
Lemma lem2290903 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2290904 (x : real) : (term113 x) = (term118 x).
Proof. exact (MK_COMB (@lem2290903) (@lem2290902 x)). Qed.
Lemma lem2290905 (x : real) : (term112 x) = (term118 x).
Proof. exact (TRANS (@lem2290897 x) (@lem2290904 x)). Qed.
Lemma lem2290906 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun n : nat => @lem2290895 x n)). Qed.
Lemma lem2290907 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2290908 (x : real) : (term94 x) = (term94 x).
Proof. exact (MK_COMB (@lem2290907) (@lem2290906 x)). Qed.
Lemma lem2290909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2290910 (x : real) : (term119 x) = (term120 x).
Proof. exact (MK_COMB (@lem2290909) (@lem2290890 x)). Qed.
Lemma lem2290911 (x : real) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem2290910 x) (@lem2290905 x)). Qed.
Lemma lem2290912 (x : real) : (term123 x) = (term121 x).
Proof. exact (@lem17160 (term89 x) (term94 x)). Qed.
Lemma lem2290913 (x : real) : (term123 x) = (term122 x).
Proof. exact (TRANS (@lem2290912 x) (@lem2290911 x)). Qed.
Lemma lem2290914 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2290915 (x : real) : (term91 x) = (term91 x).
Proof. exact (MK_COMB (@lem2290914) (@lem2290893 x)). Qed.
Lemma lem2290916 (x : real) : (term95 x) = (term95 x).
Proof. exact (MK_COMB (@lem2290915 x) (@lem2290908 x)). Qed.
Lemma lem2290918 (x : real) : (term124 x) = (term124 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem2290919 (x : real) : (term125 x) = (term125 x).
Proof. exact (MK_COMB (@lem2290918 x) (@lem2290916 x)). Qed.
Lemma lem2290921 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem2290922 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem2290921 x) (@lem2290913 x)). Qed.
Lemma lem2290923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2290924 (x : real) : (term129 x) = (term130 x).
Proof. exact (MK_COMB (@lem2290923) (@lem2290922 x)). Qed.
Lemma lem2290925 (x : real) : (term131 x) = (term132 x).
Proof. exact (MK_COMB (@lem2290924 x) (@lem2290919 x)). Qed.
Lemma lem2290926 (x : real) : ((integer x) = (term95 x)) = (term131 x).
Proof. exact (@lem17784 (integer x) (term95 x)). Qed.
Lemma lem2290927 (x : real) : ((integer x) = (term95 x)) = (term132 x).
Proof. exact (TRANS (@lem2290926 x) (@lem2290925 x)). Qed.
Lemma lem2290928 : term98 = term133.
Proof. exact (fun_ext (fun x : real => @lem2290927 x)). Qed.
Lemma lem2290929 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290930 : term99 = term134.
Proof. exact (MK_COMB (@lem2290929) (@lem2290928)). Qed.
Lemma lem2290932 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term135 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem2290933 (P : real -> Prop) (Q : real -> Prop) : (term137 P Q) = (term138 P Q).
Proof. exact (@lem2290932 real P Q). Qed.
Lemma lem2290934 : term139 = term140.
Proof. exact (@lem2290933 term141 term142). Qed.
Lemma lem2290935 (x : real) : (term143 x) = (term128 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem2290936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2290937 (x : real) : (term144 x) = (term130 x).
Proof. exact (MK_COMB (@lem2290936) (@lem2290935 x)). Qed.
Lemma lem2290938 (x : real) : (term145 x) = (term125 x).
Proof. exact (eq_refl (term145 x)). Qed.
Lemma lem2290939 (x : real) : (term146 x) = (term132 x).
Proof. exact (MK_COMB (@lem2290937 x) (@lem2290938 x)). Qed.
Lemma lem2290940 : term147 = term133.
Proof. exact (fun_ext (fun x : real => @lem2290939 x)). Qed.
Lemma lem2290941 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290942 : term139 = term134.
Proof. exact (MK_COMB (@lem2290941) (@lem2290940)). Qed.
Lemma lem2290943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2290944 : term148 = term149.
Proof. exact (MK_COMB (@lem2290943) (@lem2290942)). Qed.
Lemma lem2290945 (x : real) : (term143 x) = (term128 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem2290946 : term150 = term141.
Proof. exact (fun_ext (fun x : real => @lem2290945 x)). Qed.
Lemma lem2290947 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290948 : term151 = term152.
Proof. exact (MK_COMB (@lem2290947) (@lem2290946)). Qed.
Lemma lem2290949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2290950 : term153 = term154.
Proof. exact (MK_COMB (@lem2290949) (@lem2290948)). Qed.
Lemma lem2290951 (x : real) : (term145 x) = (term125 x).
Proof. exact (eq_refl (term145 x)). Qed.
Lemma lem2290952 : term155 = term142.
Proof. exact (fun_ext (fun x : real => @lem2290951 x)). Qed.
Lemma lem2290953 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2290954 : term156 = term157.
Proof. exact (MK_COMB (@lem2290953) (@lem2290952)). Qed.
Lemma lem2290955 : term140 = term158.
Proof. exact (MK_COMB (@lem2290950) (@lem2290954)). Qed.
Lemma lem2290956 : (term139 = term140) = (term134 = term158).
Proof. exact (MK_COMB (@lem2290944) (@lem2290955)). Qed.
Lemma lem2290957 : term134 = term158.
Proof. exact (EQ_MP (@lem2290956) (@lem2290934)). Qed.
Lemma lem2291051 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term68 A P Q) = (term67 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2291052 (P : nat -> Prop) (Q : nat -> Prop) : (term70 P Q) = (term69 P Q).
Proof. exact (@lem2291051 nat P Q). Qed.
Lemma lem2291053 (x : real) : (term72 x) = (term71 x).
Proof. exact (@lem2291052 (term73 x) (term74 x)). Qed.
Lemma lem2291054 (x : real) (n : nat) : (term75 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term75 x n)). Qed.
Lemma lem2291055 (x : real) : (term87 x) = (term73 x).
Proof. exact (fun_ext (fun n : nat => @lem2291054 x n)). Qed.
Lemma lem2291056 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2291057 (x : real) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem2291056) (@lem2291055 x)). Qed.
Lemma lem2291058 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2291059 (x : real) : (term90 x) = (term91 x).
Proof. exact (MK_COMB (@lem2291058) (@lem2291057 x)). Qed.
Lemma lem2291060 (x : real) (n : nat) : (term78 x n) = (x = (term79 n)).
Proof. exact (eq_refl (term78 x n)). Qed.
Lemma lem2291061 (x : real) : (term92 x) = (term74 x).
Proof. exact (fun_ext (fun n : nat => @lem2291060 x n)). Qed.
Lemma lem2291062 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2291063 (x : real) : (term93 x) = (term94 x).
Proof. exact (MK_COMB (@lem2291062) (@lem2291061 x)). Qed.
Lemma lem2291064 (x : real) : (term72 x) = (term95 x).
Proof. exact (MK_COMB (@lem2291059 x) (@lem2291063 x)). Qed.
Lemma lem2291065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2291066 (x : real) : (term159 x) = (term160 x).
Proof. exact (MK_COMB (@lem2291065) (@lem2291064 x)). Qed.
Lemma lem2291067 (x : real) (n : nat) : (term75 x n) = (x = (real_of_num n)).
Proof. exact (eq_refl (term75 x n)). Qed.
Lemma lem2291068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2291069 (x : real) (n : nat) : (term76 x n) = (term77 x n).
Proof. exact (MK_COMB (@lem2291068) (@lem2291067 x n)). Qed.
Lemma lem2291070 (x : real) (n : nat) : (term78 x n) = (x = (term79 n)).
Proof. exact (eq_refl (term78 x n)). Qed.
Lemma lem2291071 (x : real) (n : nat) : (term80 x n) = (term81 x n).
Proof. exact (MK_COMB (@lem2291069 x n) (@lem2291070 x n)). Qed.
Lemma lem2291072 (x : real) : (term82 x) = (term83 x).
Proof. exact (fun_ext (fun n : nat => @lem2291071 x n)). Qed.
Lemma lem2291073 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2291074 (x : real) : (term71 x) = (term84 x).
Proof. exact (MK_COMB (@lem2291073) (@lem2291072 x)). Qed.
Lemma lem2291075 (x : real) : ((term72 x) = (term71 x)) = ((term95 x) = (term84 x)).
Proof. exact (MK_COMB (@lem2291066 x) (@lem2291074 x)). Qed.
Lemma lem2291076 (x : real) : (term95 x) = (term84 x).
Proof. exact (EQ_MP (@lem2291075 x) (@lem2291053 x)). Qed.
Lemma lem2291077 (x : real) : (term124 x) = (term124 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem2291078 (x : real) : (term125 x) = (term161 x).
Proof. exact (MK_COMB (@lem2291077 x) (@lem2291076 x)). Qed.
Lemma lem2291080 {A : Type'} (P : Prop) (Q : A -> Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem2291081 (P : Prop) (Q : nat -> Prop) : (term164 P Q) = (term165 P Q).
Proof. exact (@lem2291080 nat P Q). Qed.
Lemma lem2291082 (x : real) : (term166 x) = (term167 x).
Proof. exact (@lem2291081 (term168 x) (term83 x)). Qed.
Lemma lem2291083 (x : real) (n : nat) : (term169 x n) = (term81 x n).
Proof. exact (eq_refl (term169 x n)). Qed.
Lemma lem2291084 (x : real) : (term170 x) = (term83 x).
Proof. exact (fun_ext (fun n : nat => @lem2291083 x n)). Qed.
Lemma lem2291085 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2291086 (x : real) : (term171 x) = (term84 x).
Proof. exact (MK_COMB (@lem2291085) (@lem2291084 x)). Qed.
Lemma lem2291087 (x : real) : (term124 x) = (term124 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem2291088 (x : real) : (term166 x) = (term161 x).
Proof. exact (MK_COMB (@lem2291087 x) (@lem2291086 x)). Qed.
Lemma lem2291089 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2291090 (x : real) : (term172 x) = (term173 x).
Proof. exact (MK_COMB (@lem2291089) (@lem2291088 x)). Qed.
Lemma lem2291091 (x : real) (n : nat) : (term169 x n) = (term81 x n).
Proof. exact (eq_refl (term169 x n)). Qed.
Lemma lem2291092 (x : real) : (term124 x) = (term124 x).
Proof. exact (eq_refl (term124 x)). Qed.
Lemma lem2291093 (x : real) (n : nat) : (term174 x n) = (term175 x n).
Proof. exact (MK_COMB (@lem2291092 x) (@lem2291091 x n)). Qed.
Lemma lem2291094 (x : real) : (term176 x) = (term177 x).
Proof. exact (fun_ext (fun n : nat => @lem2291093 x n)). Qed.
Lemma lem2291095 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2291096 (x : real) : (term167 x) = (term178 x).
Proof. exact (MK_COMB (@lem2291095) (@lem2291094 x)). Qed.
Lemma lem2291097 (x : real) : ((term166 x) = (term167 x)) = ((term161 x) = (term178 x)).
Proof. exact (MK_COMB (@lem2291090 x) (@lem2291096 x)). Qed.
Lemma lem2291098 (x : real) : (term161 x) = (term178 x).
Proof. exact (EQ_MP (@lem2291097 x) (@lem2291082 x)). Qed.
Lemma lem2291099 (x : real) : (term125 x) = (term178 x).
Proof. exact (TRANS (@lem2291078 x) (@lem2291098 x)). Qed.
Lemma lem2291100 : term142 = term179.
Proof. exact (fun_ext (fun x : real => @lem2291099 x)). Qed.
Lemma lem2291101 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2291102 : term157 = term180.
Proof. exact (MK_COMB (@lem2291101) (@lem2291100)). Qed.
Lemma lem2291104 {A B : Type'} (P : type1413 A B) : (term181 A B P) = (term182 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem2291105 (P : type1622) : (term183 P) = (term184 P).
Proof. exact (@lem2291104 real nat P). Qed.
Lemma lem2291106 : term185 = term186.
Proof. exact (@lem2291105 term187). Qed.
Lemma lem2291107 (x : real) : (term188 x) = (term177 x).
Proof. exact (eq_refl (term188 x)). Qed.
Lemma lem2291108 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2291109 (x : real) (n : nat) : (term189 x n) = (term190 x n).
Proof. exact (MK_COMB (@lem2291107 x) (@lem2291108 n)). Qed.
Lemma lem2291110 (x : real) (n : nat) : (term190 x n) = (term175 x n).
Proof. exact (eq_refl (term190 x n)). Qed.
Lemma lem2291111 (x : real) (n : nat) : (term189 x n) = (term175 x n).
Proof. exact (TRANS (@lem2291109 x n) (@lem2291110 x n)). Qed.
Lemma lem2291112 (x : real) : (term191 x) = (term177 x).
Proof. exact (fun_ext (fun n : nat => @lem2291111 x n)). Qed.
Lemma lem2291113 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem2291114 (x : real) : (term192 x) = (term178 x).
Proof. exact (MK_COMB (@lem2291113) (@lem2291112 x)). Qed.
Lemma lem2291115 : term193 = term179.
Proof. exact (fun_ext (fun x : real => @lem2291114 x)). Qed.
Lemma lem2291116 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2291117 : term185 = term180.
Proof. exact (MK_COMB (@lem2291116) (@lem2291115)). Qed.
Lemma lem2291118 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2291119 : term194 = term195.
Proof. exact (MK_COMB (@lem2291118) (@lem2291117)). Qed.
Lemma lem2291120 (x : real) : (term188 x) = (term177 x).
Proof. exact (eq_refl (term188 x)). Qed.
Lemma lem2291121 (n : real -> nat) (x : real) : (n x) = (n x).
Proof. exact (eq_refl (n x)). Qed.
Lemma lem2291122 (n : real -> nat) (x : real) : (term196 n x) = (term197 n x).
Proof. exact (MK_COMB (@lem2291120 x) (@lem2291121 n x)). Qed.
Lemma lem2291123 (n : real -> nat) (x : real) : (term197 n x) = (term198 n x).
Proof. exact (eq_refl (term197 n x)). Qed.
Lemma lem2291124 (n : real -> nat) (x : real) : (term196 n x) = (term198 n x).
Proof. exact (TRANS (@lem2291122 n x) (@lem2291123 n x)). Qed.
Lemma lem2291125 (n : real -> nat) : (term199 n) = (term200 n).
Proof. exact (fun_ext (fun x : real => @lem2291124 n x)). Qed.
Lemma lem2291126 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2291127 (n : real -> nat) : (term201 n) = (term202 n).
Proof. exact (MK_COMB (@lem2291126) (@lem2291125 n)). Qed.
Lemma lem2291128 : term203 = term204.
Proof. exact (fun_ext (fun n : real -> nat => @lem2291127 n)). Qed.
Lemma lem2291129 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem2291130 : term186 = term205.
Proof. exact (MK_COMB (@lem2291129) (@lem2291128)). Qed.
Lemma lem2291131 : (term185 = term186) = (term180 = term205).
Proof. exact (MK_COMB (@lem2291119) (@lem2291130)). Qed.
Lemma lem2291132 : term180 = term205.
Proof. exact (EQ_MP (@lem2291131) (@lem2291106)). Qed.
Lemma lem2291133 : term157 = term205.
Proof. exact (TRANS (@lem2291102) (@lem2291132)). Qed.
Lemma lem2291134 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem2291135 : term158 = term206.
Proof. exact (MK_COMB (@lem2291134) (@lem2291133)). Qed.
Lemma lem2291137 {A : Type'} (P : Prop) (Q : A -> Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem2291138 (P : Prop) (Q : type1024) : (term209 P Q) = (term210 P Q).
Proof. exact (@lem2291137 (real -> nat) P Q). Qed.
Lemma lem2291139 : term211 = term212.
Proof. exact (@lem2291138 term152 term204). Qed.
Lemma lem2291140 (n : real -> nat) : (term213 n) = (term202 n).
Proof. exact (eq_refl (term213 n)). Qed.
Lemma lem2291141 : term214 = term204.
Proof. exact (fun_ext (fun n : real -> nat => @lem2291140 n)). Qed.
Lemma lem2291142 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem2291143 : term215 = term205.
Proof. exact (MK_COMB (@lem2291142) (@lem2291141)). Qed.
Lemma lem2291144 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem2291145 : term211 = term206.
Proof. exact (MK_COMB (@lem2291144) (@lem2291143)). Qed.
Lemma lem2291146 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2291147 : term216 = term217.
Proof. exact (MK_COMB (@lem2291146) (@lem2291145)). Qed.
Lemma lem2291148 (n : real -> nat) : (term213 n) = (term202 n).
Proof. exact (eq_refl (term213 n)). Qed.
Lemma lem2291149 : term154 = term154.
Proof. exact (eq_refl term154). Qed.
Lemma lem2291150 (n : real -> nat) : (term218 n) = (term219 n).
Proof. exact (MK_COMB (@lem2291149) (@lem2291148 n)). Qed.
Lemma lem2291151 : term220 = term221.
Proof. exact (fun_ext (fun n : real -> nat => @lem2291150 n)). Qed.
Lemma lem2291152 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem2291153 : term212 = term222.
Proof. exact (MK_COMB (@lem2291152) (@lem2291151)). Qed.
Lemma lem2291154 : (term211 = term212) = (term206 = term222).
Proof. exact (MK_COMB (@lem2291147) (@lem2291153)). Qed.
Lemma lem2291155 : term206 = term222.
Proof. exact (EQ_MP (@lem2291154) (@lem2291139)). Qed.
Lemma lem2291156 : term158 = term222.
Proof. exact (TRANS (@lem2291135) (@lem2291155)). Qed.
Lemma lem2291157 : term134 = term222.
Proof. exact (TRANS (@lem2290957) (@lem2291156)). Qed.
Lemma lem2291158 : term99 = term222.
Proof. exact (TRANS (@lem2290930) (@lem2291157)). Qed.
Lemma lem2291159 (h1 : term99) : term222.
Proof. exact (EQ_MP (@lem2291158) (@lem2290870 h1)). Qed.
Lemma lem2291160 (n : real -> nat) (h1 : term219 n) : term219 n.
Proof. exact (h1). Qed.
Lemma lem2291170 (h1 : term306) : term306.
Proof. exact (h1). Qed.
Lemma lem2291201 (n : real -> nat) (x : real) : (term198 n x) = (term198 n x).
Proof. exact (eq_refl (term198 n x)). Qed.
Lemma lem2291202 (n : real -> nat) : (term200 n) = (term200 n).
Proof. exact (fun_ext (fun x : real => @lem2291201 n x)). Qed.
Lemma lem2291203 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2291204 (n : real -> nat) : (term202 n) = (term202 n).
Proof. exact (MK_COMB (@lem2291203) (@lem2291202 n)). Qed.
Lemma lem2291215 (x : real) (n : nat) : (term115 x n) = (term115 x n).
Proof. exact (eq_refl (term115 x n)). Qed.
Lemma lem2291216 (x : real) : (term117 x) = (term117 x).
Proof. exact (fun_ext (fun n : nat => @lem2291215 x n)). Qed.
Lemma lem2291217 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2291218 (x : real) : (term118 x) = (term118 x).
Proof. exact (MK_COMB (@lem2291217) (@lem2291216 x)). Qed.
Lemma lem2291227 (x : real) (n : nat) : (term108 x n) = (term108 x n).
Proof. exact (eq_refl (term108 x n)). Qed.
Lemma lem2291228 (x : real) : (term110 x) = (term110 x).
Proof. exact (fun_ext (fun n : nat => @lem2291227 x n)). Qed.
Lemma lem2291229 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2291230 (x : real) : (term111 x) = (term111 x).
Proof. exact (MK_COMB (@lem2291229) (@lem2291228 x)). Qed.
Lemma lem2291231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2291232 (x : real) : (term120 x) = (term120 x).
Proof. exact (MK_COMB (@lem2291231) (@lem2291230 x)). Qed.
Lemma lem2291233 (x : real) : (term122 x) = (term122 x).
Proof. exact (MK_COMB (@lem2291232 x) (@lem2291218 x)). Qed.
Lemma lem2291238 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem2291239 (x : real) : (term128 x) = (term128 x).
Proof. exact (MK_COMB (@lem2291238 x) (@lem2291233 x)). Qed.
Lemma lem2291240 : term141 = term141.
Proof. exact (fun_ext (fun x : real => @lem2291239 x)). Qed.
Lemma lem2291241 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2291242 : term152 = term152.
Proof. exact (MK_COMB (@lem2291241) (@lem2291240)). Qed.
Lemma lem2291243 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2291244 : term154 = term154.
Proof. exact (MK_COMB (@lem2291243) (@lem2291242)). Qed.
Lemma lem2291245 (n : real -> nat) : (term219 n) = (term219 n).
Proof. exact (MK_COMB (@lem2291244) (@lem2291204 n)). Qed.
Lemma lem2291246 (n : real -> nat) (h1 : term219 n) : term219 n.
Proof. exact (EQ_MP (@lem2291245 n) (@lem2291160 n h1)). Qed.
Lemma lem2291248 (n : real -> nat) (h1 : term219 n) : term152.
Proof. exact (proj1 (@lem2291246 n h1)). Qed.
Lemma lem2291252 (h1 : term306) : term306.
Proof. exact (h1). Qed.
Lemma lem2291254 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term136 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem2291255 (P : nat -> Prop) (Q : nat -> Prop) : (term223 P Q) = (term224 P Q).
Proof. exact (@lem2291254 nat P Q). Qed.
Lemma lem2291256 (x : real) : (term225 x) = (term226 x).
Proof. exact (@lem2291255 (term110 x) (term117 x)). Qed.
Lemma lem2291257 (x : real) (n : nat) : (term227 x n) = (term108 x n).
Proof. exact (eq_refl (term227 x n)). Qed.
Lemma lem2291258 (x : real) : (term228 x) = (term110 x).
Proof. exact (fun_ext (fun n : nat => @lem2291257 x n)). Qed.
Lemma lem2291259 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2291260 (x : real) : (term229 x) = (term111 x).
Proof. exact (MK_COMB (@lem2291259) (@lem2291258 x)). Qed.
Lemma lem2291261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2291262 (x : real) : (term230 x) = (term120 x).
Proof. exact (MK_COMB (@lem2291261) (@lem2291260 x)). Qed.
Lemma lem2291263 (x : real) (n : nat) : (term231 x n) = (term115 x n).
Proof. exact (eq_refl (term231 x n)). Qed.
Lemma lem2291264 (x : real) : (term232 x) = (term117 x).
Proof. exact (fun_ext (fun n : nat => @lem2291263 x n)). Qed.
Lemma lem2291265 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2291266 (x : real) : (term233 x) = (term118 x).
Proof. exact (MK_COMB (@lem2291265) (@lem2291264 x)). Qed.
Lemma lem2291267 (x : real) : (term225 x) = (term122 x).
Proof. exact (MK_COMB (@lem2291262 x) (@lem2291266 x)). Qed.
Lemma lem2291268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2291269 (x : real) : (term234 x) = (term235 x).
Proof. exact (MK_COMB (@lem2291268) (@lem2291267 x)). Qed.
Lemma lem2291270 (x : real) (n : nat) : (term227 x n) = (term108 x n).
Proof. exact (eq_refl (term227 x n)). Qed.
Lemma lem2291271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2291272 (x : real) (n : nat) : (term236 x n) = (term237 x n).
Proof. exact (MK_COMB (@lem2291271) (@lem2291270 x n)). Qed.
Lemma lem2291273 (x : real) (n : nat) : (term231 x n) = (term115 x n).
Proof. exact (eq_refl (term231 x n)). Qed.
Lemma lem2291274 (x : real) (n : nat) : (term238 x n) = (term239 x n).
Proof. exact (MK_COMB (@lem2291272 x n) (@lem2291273 x n)). Qed.
Lemma lem2291275 (x : real) : (term240 x) = (term241 x).
Proof. exact (fun_ext (fun n : nat => @lem2291274 x n)). Qed.
Lemma lem2291276 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2291277 (x : real) : (term226 x) = (term242 x).
Proof. exact (MK_COMB (@lem2291276) (@lem2291275 x)). Qed.
Lemma lem2291278 (x : real) : ((term225 x) = (term226 x)) = ((term122 x) = (term242 x)).
Proof. exact (MK_COMB (@lem2291269 x) (@lem2291277 x)). Qed.
Lemma lem2291279 (x : real) : (term122 x) = (term242 x).
Proof. exact (EQ_MP (@lem2291278 x) (@lem2291256 x)). Qed.
Lemma lem2291280 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem2291281 (x : real) : (term128 x) = (term243 x).
Proof. exact (MK_COMB (@lem2291280 x) (@lem2291279 x)). Qed.
Lemma lem2291283 {A : Type'} (P : Prop) (Q : A -> Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem2291284 (P : Prop) (Q : nat -> Prop) : (term246 P Q) = (term247 P Q).
Proof. exact (@lem2291283 nat P Q). Qed.
Lemma lem2291285 (x : real) : (term248 x) = (term249 x).
Proof. exact (@lem2291284 (integer x) (term241 x)). Qed.
Lemma lem2291286 (x : real) (n : nat) : (term250 x n) = (term239 x n).
Proof. exact (eq_refl (term250 x n)). Qed.
Lemma lem2291287 (x : real) : (term251 x) = (term241 x).
Proof. exact (fun_ext (fun n : nat => @lem2291286 x n)). Qed.
Lemma lem2291288 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2291289 (x : real) : (term252 x) = (term242 x).
Proof. exact (MK_COMB (@lem2291288) (@lem2291287 x)). Qed.
Lemma lem2291290 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem2291291 (x : real) : (term248 x) = (term243 x).
Proof. exact (MK_COMB (@lem2291290 x) (@lem2291289 x)). Qed.
Lemma lem2291292 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2291293 (x : real) : (term253 x) = (term254 x).
Proof. exact (MK_COMB (@lem2291292) (@lem2291291 x)). Qed.
Lemma lem2291294 (x : real) (n : nat) : (term250 x n) = (term239 x n).
Proof. exact (eq_refl (term250 x n)). Qed.
Lemma lem2291295 (x : real) : (term126 x) = (term126 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem2291296 (x : real) (n : nat) : (term255 x n) = (term256 x n).
Proof. exact (MK_COMB (@lem2291295 x) (@lem2291294 x n)). Qed.
Lemma lem2291297 (x : real) : (term257 x) = (term258 x).
Proof. exact (fun_ext (fun n : nat => @lem2291296 x n)). Qed.
Lemma lem2291298 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2291299 (x : real) : (term249 x) = (term259 x).
Proof. exact (MK_COMB (@lem2291298) (@lem2291297 x)). Qed.
Lemma lem2291300 (x : real) : ((term248 x) = (term249 x)) = ((term243 x) = (term259 x)).
Proof. exact (MK_COMB (@lem2291293 x) (@lem2291299 x)). Qed.
Lemma lem2291301 (x : real) : (term243 x) = (term259 x).
Proof. exact (EQ_MP (@lem2291300 x) (@lem2291285 x)). Qed.
Lemma lem2291302 (x : real) : (term128 x) = (term259 x).
Proof. exact (TRANS (@lem2291281 x) (@lem2291301 x)). Qed.
Lemma lem2291303 : term141 = term260.
Proof. exact (fun_ext (fun x : real => @lem2291302 x)). Qed.
Lemma lem2291304 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2291305 : term152 = term261.
Proof. exact (MK_COMB (@lem2291304) (@lem2291303)). Qed.
Lemma lem2291322 (x : real) (n : nat) : (term256 x n) = (term262 x n).
Proof. exact (@lem19490 (term108 x n) (integer x) (term115 x n)). Qed.
Lemma lem2291323 (x : real) : (term258 x) = (term263 x).
Proof. exact (fun_ext (fun n : nat => @lem2291322 x n)). Qed.
Lemma lem2291324 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2291325 (x : real) : (term259 x) = (term264 x).
Proof. exact (MK_COMB (@lem2291324) (@lem2291323 x)). Qed.
Lemma lem2291326 : term260 = term265.
Proof. exact (fun_ext (fun x : real => @lem2291325 x)). Qed.
Lemma lem2291327 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2291328 : term261 = term266.
Proof. exact (MK_COMB (@lem2291327) (@lem2291326)). Qed.
Lemma lem2291329 : term152 = term266.
Proof. exact (TRANS (@lem2291305) (@lem2291328)). Qed.
Lemma lem2291330 (n : real -> nat) (h1 : term219 n) : term266.
Proof. exact (EQ_MP (@lem2291329) (@lem2291248 n h1)). Qed.
Lemma lem2291350 (_28798 : real) (n : real -> nat) (h1 : term219 n) : term267 _28798.
Proof. exact (@lem2291330 n h1 _28798). Qed.
Lemma lem2291351 (_28798 : real) : (term267 _28798) = (term264 _28798).
Proof. exact (eq_refl (term267 _28798)). Qed.
Lemma lem2291352 (_28798 : real) (n : real -> nat) (h1 : term219 n) : term264 _28798.
Proof. exact (EQ_MP (@lem2291351 _28798) (@lem2291350 _28798 n h1)). Qed.
Lemma lem2291353 (_28798 : real) (_28799 : nat) (n : real -> nat) (h1 : term219 n) : term268 _28798 _28799.
Proof. exact (@lem2291352 _28798 n h1 _28799). Qed.
Lemma lem2291354 (_28798 : real) (_28799 : nat) : (term268 _28798 _28799) = (term262 _28798 _28799).
Proof. exact (eq_refl (term268 _28798 _28799)). Qed.
Lemma lem2291355 (_28798 : real) (_28799 : nat) (n : real -> nat) (h1 : term219 n) : term262 _28798 _28799.
Proof. exact (EQ_MP (@lem2291354 _28798 _28799) (@lem2291353 _28798 _28799 n h1)). Qed.
Lemma lem2291362 (h1 : term306) : term306.
Proof. exact (h1). Qed.
Lemma lem2291378 (_28798 : real) (_28799 : nat) (n : real -> nat) (h1 : term219 n) : term269 _28798 _28799.
Proof. exact (proj1 (@lem2291355 _28798 _28799 n h1)). Qed.
Lemma lem2291434 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem2291435 : term42 = term42.
Proof. exact (@lem2291434 term42). Qed.
Lemma lem2291436 : term313.
Proof. exact (fun h0 : term314 => @lem2291435). Qed.
Lemma lem2291438 (p : Prop) : (term272 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2291439 : term313 = (term42 = term42).
Proof. exact (@lem2291438 (term42 = term42)). Qed.
Lemma lem2291440 : term42 = term42.
Proof. exact (EQ_MP (@lem2291439) (@lem2291436)). Qed.
Lemma lem2291442 (b : Prop) (a : Prop) : (a \/ b) = (term273 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2291443 (_28799 : nat) (_28798 : real) : (term269 _28798 _28799) = (term274 _28799 _28798).
Proof. exact (@lem2291442 (term108 _28798 _28799) (integer _28798)). Qed.
Lemma lem2291445 (a : Prop) : (term275 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2291446 (_28798 : real) (_28799 : nat) : (term276 _28798 _28799) = (_28798 = (real_of_num _28799)).
Proof. exact (@lem2291445 (_28798 = (real_of_num _28799))). Qed.
Lemma lem2291447 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2291448 (_28798 : real) (_28799 : nat) : (term277 _28798 _28799) = (term278 _28798 _28799).
Proof. exact (MK_COMB (@lem2291447) (@lem2291446 _28798 _28799)). Qed.
Lemma lem2291449 (_28798 : real) : (integer _28798) = (integer _28798).
Proof. exact (eq_refl (integer _28798)). Qed.
Lemma lem2291450 (_28799 : nat) (_28798 : real) : (term274 _28799 _28798) = (term279 _28799 _28798).
Proof. exact (MK_COMB (@lem2291448 _28798 _28799) (@lem2291449 _28798)). Qed.
Lemma lem2291451 (_28799 : nat) (_28798 : real) : (term269 _28798 _28799) = (term279 _28799 _28798).
Proof. exact (TRANS (@lem2291443 _28799 _28798) (@lem2291450 _28799 _28798)). Qed.
Lemma lem2291454 (_28799 : nat) (_28798 : real) (n : real -> nat) (h1 : term219 n) : term279 _28799 _28798.
Proof. exact (EQ_MP (@lem2291451 _28799 _28798) (@lem2291378 _28798 _28799 n h1)). Qed.
Lemma lem2291455 (n : real -> nat) (h1 : term219 n) : term315.
Proof. exact (@lem2291454 (NUMERAL 0) term42 n h1). Qed.
Lemma lem2291458 (n : real -> nat) (h1 : term219 n) : term44.
Proof. exact (@lem2291455 n h1 (@lem2291440)). Qed.
Lemma lem2291459 (n : real -> nat) (h1 : term219 n) : term316.
Proof. exact (fun h0 : term306 => @lem2291458 n h1). Qed.
Lemma lem2291461 (p : Prop) : (term272 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2291462 : term316 = term44.
Proof. exact (@lem2291461 term44). Qed.
Lemma lem2291463 (n : real -> nat) (h1 : term219 n) : term44.
Proof. exact (EQ_MP (@lem2291462) (@lem2291459 n h1)). Qed.
Lemma lem2291466 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2291468 : term306 = term317.
Proof. exact (@lem2291466 term44). Qed.
Lemma lem2291471 (h1 : term306) : term317.
Proof. exact (EQ_MP (@lem2291468) (@lem2291362 h1)). Qed.
Lemma lem2291474 (n : real -> nat) (h1 : term306) (h2 : term219 n) : False.
Proof. exact (@lem2291471 h1 (@lem2291463 n h2)). Qed.
Lemma lem2291475 (n : real -> nat) (h1 : term306) (h2 : term219 n) : term284.
Proof. exact (fun h0 : ~ False => @lem2291474 n h1 h2). Qed.
Lemma lem2291477 (p : Prop) : (term272 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2291478 : term284 = False.
Proof. exact (@lem2291477 False). Qed.
Lemma lem2291479 (n : real -> nat) (h1 : term306) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2291478) (@lem2291475 n h1 h2)). Qed.
Lemma lem2291480 (n : real -> nat) (h1 : term306) (h2 : term219 n) : term306 = False.
Proof. exact (prop_ext (fun h3 : term306 => @lem2291479 n h1 h2) (fun h3 : False => @lem2291362 h1)). Qed.
Lemma lem2291481 (n : real -> nat) (h1 : term306) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2291480 n h1 h2) (@lem2291362 h1)). Qed.
Lemma lem2291482 (n : real -> nat) (h1 : term306) (h2 : term219 n) : term306 = False.
Proof. exact (prop_ext (fun h3 : term306 => @lem2291481 n h1 h2) (fun h3 : False => @lem2291252 h1)). Qed.
Lemma lem2291483 (n : real -> nat) (h1 : term306) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2291482 n h1 h2) (@lem2291252 h1)). Qed.
Lemma lem2291484 (n : real -> nat) (h1 : term306) (h2 : term219 n) : term306 = False.
Proof. exact (prop_ext (fun h3 : term306 => @lem2291483 n h1 h2) (fun h3 : False => @lem2291252 h1)). Qed.
Lemma lem2291485 (n : real -> nat) (h1 : term306) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2291484 n h1 h2) (@lem2291252 h1)). Qed.
Lemma lem2291486 (n : real -> nat) (h1 : term306) (h2 : term219 n) : (term219 n) = False.
Proof. exact (prop_ext (fun h3 : term219 n => @lem2291485 n h1 h2) (fun h3 : False => @lem2291246 n h2)). Qed.
Lemma lem2291487 (n : real -> nat) (h1 : term306) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2291486 n h1 h2) (@lem2291246 n h2)). Qed.
Lemma lem2291488 (n : real -> nat) (h1 : term306) (h2 : term219 n) : term306 = False.
Proof. exact (prop_ext (fun h3 : term306 => @lem2291487 n h1 h2) (fun h3 : False => @lem2291170 h1)). Qed.
Lemma lem2291489 (n : real -> nat) (h1 : term306) (h2 : term219 n) : False.
Proof. exact (EQ_MP (@lem2291488 n h1 h2) (@lem2291170 h1)). Qed.
Lemma lem2291490 (h1 : term99) (h2 : term306) : False.
Proof. exact (ex_elim (@lem2291159 h1) (fun n : real -> nat => fun h0 : term221 n => @lem2291489 n h2 h0)). Qed.
Lemma lem2291491 (h1 : term99) (h2 : term306) : term306 = False.
Proof. exact (prop_ext (fun h3 : term306 => @lem2291490 h1 h2) (fun h3 : False => @lem2290876 h2)). Qed.
Lemma lem2291492 (h1 : term99) (h2 : term306) : False.
Proof. exact (EQ_MP (@lem2291491 h1 h2) (@lem2290876 h2)). Qed.
Lemma lem2291493 (h1 : term306) : term285.
Proof. exact (fun h0 : term99 => @lem2291492 h0 h1). Qed.
Lemma lem2291494 : term285 = term100.
Proof. exact (@lem69 term99). Qed.
Lemma lem2291495 (h1 : term306) : term100.
Proof. exact (EQ_MP (@lem2291494) (@lem2291493 h1)). Qed.
Lemma lem2291496 : term312.
Proof. exact (fun h0 : term306 => @lem2291495 h0). Qed.
Lemma lem2291497 : term307.
Proof. exact (EQ_MP (@lem2290868) (@lem2291496)). Qed.
Lemma lem2291499 : term307.
Proof. exact (@lem2290750 (@lem2291497)). Qed.
Lemma lem2291500 (h1 : term306) : term65.
Proof. exact (@lem2291499 (@lem2290735 h1)). Qed.
Lemma lem2291501 (h1 : term306) : False.
Proof. exact (@lem2291500 h1 (@lem2288999)). Qed.
Lemma lem2291502 (h1 : term306) : term306 = False.
Proof. exact (prop_ext (fun h2 : term306 => @lem2291501 h1) (fun h2 : False => @lem2290735 h1)). Qed.
Lemma lem2291503 (h1 : term306) : False.
Proof. exact (EQ_MP (@lem2291502 h1) (@lem2290735 h1)). Qed.
Lemma lem2291504 : term305.
Proof. exact (fun h0 : term306 => @lem2291503 h0). Qed.
Lemma lem2291508 : term44.
Proof. exact (EQ_MP (@lem2290734) (@lem2291504)). Qed.
Lemma lem2291509 (x : int) : term47 x.
Proof. exact (fun h0 : term318 x => @lem2291508). Qed.
Lemma lem2291510 : term49.
Proof. exact (EQ_MP (@lem2289947) (@lem2290729)). Qed.
Lemma lem2291511 (x : int) : term52 x.
Proof. exact (fun h0 : term41 x => @lem2291510). Qed.
Lemma lem2291512 (x : int) : term55 x.
Proof. exact (conj (@lem2291511 x) (@lem2291509 x)). Qed.
Lemma lem2291516 (x : int) : term25 x.
Proof. exact (EQ_MP (@lem2289112 x) (@lem2291512 x)). Qed.
Lemma lem2291517 (x : int) : term28 x.
Proof. exact (fun h0 : term319 x => @lem2291516 x). Qed.
Lemma lem2291518 : term30.
Proof. exact (EQ_MP (@lem2289162) (@lem2289942)). Qed.
Lemma lem2291519 (x : int) : term33 x.
Proof. exact (fun h0 : term22 x => @lem2291518). Qed.
Lemma lem2291520 (x : int) : term36 x.
Proof. exact (conj (@lem2291519 x) (@lem2291517 x)). Qed.
Lemma lem2291521 (x : int) : term13 x.
Proof. exact (EQ_MP (@lem2289052 x) (@lem2291520 x)). Qed.
Lemma lem2291522 (x : int) : (term9 x) = (term6 x).
Proof. exact (EQ_MP (@lem2289034 x) (@lem2291521 x)). Qed.
Lemma lem2291527 : term320.
Proof. exact (fun x : int => @lem2291522 x). Qed.
