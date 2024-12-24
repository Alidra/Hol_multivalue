Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_REM_POS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INT_DIVISION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem2394142 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2394143 : term1 = term2.
Proof. exact (@lem2394142 term1). Qed.
Lemma lem2394144 : term2 = term1.
Proof. exact (SYM (@lem2394143)). Qed.
Lemma lem2394145 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2394148 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2394149 : term5.
Proof. exact (fun h0 : term4 => @lem2394148 h0). Qed.
Lemma lem2394150 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2394151 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2394152 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2394150 h2 (@lem2394151 h1)). Qed.
Lemma lem2394153 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem2394152 h1 h0). Qed.
Lemma lem2394154 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2394155 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2394153 h1 (@lem2394154 h2)). Qed.
Lemma lem2394156 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem2394155 h0 h1). Qed.
Lemma lem2394157 : term7.
Proof. exact (fun h0 : term5 => @lem2394156 h0). Qed.
Lemma lem2394160 : term5.
Proof. exact (@lem2394157 (@lem2394149)). Qed.
Lemma lem2394174 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2394175 : term8 = term9.
Proof. exact (@lem2394174 term10). Qed.
Lemma lem2394190 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem2394197 : term4 = term12.
Proof. exact (MK_COMB (@lem2394190) (@lem2394175)). Qed.
Lemma lem2394212 (m : int) (n : int) : (term13 m n) = (term13 m n).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem2394213 (m : int) : (term14 m) = (term14 m).
Proof. exact (fun_ext (fun n : int => @lem2394212 m n)). Qed.
Lemma lem2394214 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2394215 (m : int) : (term15 m) = (term15 m).
Proof. exact (MK_COMB (@lem2394214) (@lem2394213 m)). Qed.
Lemma lem2394216 : term16 = term16.
Proof. exact (fun_ext (fun m : int => @lem2394215 m)). Qed.
Lemma lem2394217 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2394218 : term10 = term10.
Proof. exact (MK_COMB (@lem2394217) (@lem2394216)). Qed.
Lemma lem2394219 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2394220 : term9 = term9.
Proof. exact (MK_COMB (@lem2394219) (@lem2394218)). Qed.
Lemma lem2394227 (a : int) (b : int) : (term17 a b) = (term17 a b).
Proof. exact (eq_refl (term17 a b)). Qed.
Lemma lem2394228 (a : int) : (term18 a) = (term18 a).
Proof. exact (fun_ext (fun b : int => @lem2394227 a b)). Qed.
Lemma lem2394229 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2394230 (a : int) : (term19 a) = (term19 a).
Proof. exact (MK_COMB (@lem2394229) (@lem2394228 a)). Qed.
Lemma lem2394231 : term20 = term20.
Proof. exact (fun_ext (fun a : int => @lem2394230 a)). Qed.
Lemma lem2394232 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2394233 : term1 = term1.
Proof. exact (MK_COMB (@lem2394232) (@lem2394231)). Qed.
Lemma lem2394234 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2394235 : term3 = term3.
Proof. exact (MK_COMB (@lem2394234) (@lem2394233)). Qed.
Lemma lem2394236 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2394237 : term11 = term11.
Proof. exact (MK_COMB (@lem2394236) (@lem2394235)). Qed.
Lemma lem2394238 : term12 = term12.
Proof. exact (MK_COMB (@lem2394237) (@lem2394220)). Qed.
Lemma lem2394275 : term4 = term12.
Proof. exact (TRANS (@lem2394197) (@lem2394238)). Qed.
Lemma lem2394276 : term12 = term4.
Proof. exact (SYM (@lem2394275)). Qed.
Lemma lem2394277 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2394278 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem2394285 (a : int) (b : int) : (term21 a b) = (term22 a b).
Proof. exact (@lem17362 (term23 b) (term24 a b)). Qed.
Lemma lem2394286 (P : int -> Prop) : (term25 P) = (term26 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2394287 (a : int) : (term27 a) = (term28 a).
Proof. exact (@lem2394286 (term18 a)). Qed.
Lemma lem2394288 (a : int) (b : int) : (term29 a b) = (term17 a b).
Proof. exact (eq_refl (term29 a b)). Qed.
Lemma lem2394289 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2394290 (a : int) (b : int) : (term30 a b) = (term21 a b).
Proof. exact (MK_COMB (@lem2394289) (@lem2394288 a b)). Qed.
Lemma lem2394291 (a : int) (b : int) : (term30 a b) = (term22 a b).
Proof. exact (TRANS (@lem2394290 a b) (@lem2394285 a b)). Qed.
Lemma lem2394292 (a : int) : (term31 a) = (term32 a).
Proof. exact (fun_ext (fun b : int => @lem2394291 a b)). Qed.
Lemma lem2394293 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2394294 (a : int) : (term28 a) = (term33 a).
Proof. exact (MK_COMB (@lem2394293) (@lem2394292 a)). Qed.
Lemma lem2394295 (a : int) : (term27 a) = (term33 a).
Proof. exact (TRANS (@lem2394287 a) (@lem2394294 a)). Qed.
Lemma lem2394296 (P : int -> Prop) : (term25 P) = (term26 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2394297 : term3 = term34.
Proof. exact (@lem2394296 term20). Qed.
Lemma lem2394298 (a : int) : (term35 a) = (term19 a).
Proof. exact (eq_refl (term35 a)). Qed.
Lemma lem2394299 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2394300 (a : int) : (term36 a) = (term27 a).
Proof. exact (MK_COMB (@lem2394299) (@lem2394298 a)). Qed.
Lemma lem2394301 (a : int) : (term36 a) = (term33 a).
Proof. exact (TRANS (@lem2394300 a) (@lem2394295 a)). Qed.
Lemma lem2394302 : term37 = term38.
Proof. exact (fun_ext (fun a : int => @lem2394301 a)). Qed.
Lemma lem2394303 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2394304 : term34 = term39.
Proof. exact (MK_COMB (@lem2394303) (@lem2394302)). Qed.
Lemma lem2394361 : term3 = term39.
Proof. exact (TRANS (@lem2394297) (@lem2394304)). Qed.
Lemma lem2394362 (h1 : term3) : term39.
Proof. exact (EQ_MP (@lem2394361) (@lem2394277 h1)). Qed.
Lemma lem2394365 (n : int) : (term40 n) = (n = term41).
Proof. exact (@lem16933 (n = term41)). Qed.
Lemma lem2394374 (m : int) (n : int) : (term42 m n) = (term42 m n).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem2394375 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2394376 (n : int) : (term43 n) = (term44 n).
Proof. exact (MK_COMB (@lem2394375) (@lem2394365 n)). Qed.
Lemma lem2394377 (m : int) (n : int) : (term45 m n) = (term46 m n).
Proof. exact (MK_COMB (@lem2394376 n) (@lem2394374 m n)). Qed.
Lemma lem2394378 (m : int) (n : int) : (term13 m n) = (term45 m n).
Proof. exact (@lem17265 (term23 n) (term42 m n)). Qed.
Lemma lem2394379 (m : int) (n : int) : (term13 m n) = (term46 m n).
Proof. exact (TRANS (@lem2394378 m n) (@lem2394377 m n)). Qed.
Lemma lem2394380 (m : int) : (term14 m) = (term47 m).
Proof. exact (fun_ext (fun n : int => @lem2394379 m n)). Qed.
Lemma lem2394381 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2394382 (m : int) : (term15 m) = (term48 m).
Proof. exact (MK_COMB (@lem2394381) (@lem2394380 m)). Qed.
Lemma lem2394383 : term16 = term49.
Proof. exact (fun_ext (fun m : int => @lem2394382 m)). Qed.
Lemma lem2394384 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2394441 : term10 = term50.
Proof. exact (MK_COMB (@lem2394384) (@lem2394383)). Qed.
Lemma lem2394442 (h1 : term10) : term50.
Proof. exact (EQ_MP (@lem2394441) (@lem2394278 h1)). Qed.
Lemma lem2394443 (a : int) (h1 : term33 a) : term33 a.
Proof. exact (h1). Qed.
Lemma lem2394507 (m : int) (n : int) : (term46 m n) = (term46 m n).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem2394508 (m : int) : (term47 m) = (term47 m).
Proof. exact (fun_ext (fun n : int => @lem2394507 m n)). Qed.
Lemma lem2394509 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2394510 (m : int) : (term48 m) = (term48 m).
Proof. exact (MK_COMB (@lem2394509) (@lem2394508 m)). Qed.
Lemma lem2394511 : term49 = term49.
Proof. exact (fun_ext (fun m : int => @lem2394510 m)). Qed.
Lemma lem2394512 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2394513 : term50 = term50.
Proof. exact (MK_COMB (@lem2394512) (@lem2394511)). Qed.
Lemma lem2394514 (h1 : term10) : term50.
Proof. exact (EQ_MP (@lem2394513) (@lem2394442 h1)). Qed.
Lemma lem2394544 (a : int) (b : int) (h1 : term22 a b) : term22 a b.
Proof. exact (h1). Qed.
Lemma lem2394561 (m : int) (n : int) : (term46 m n) = (term51 m n).
Proof. exact (@lem19490 (m = (term52 m n)) (n = term41) (term53 m n)). Qed.
Lemma lem2394568 (m : int) (n : int) : (term54 m n) = (term55 m n).
Proof. exact (@lem19490 (term24 m n) (n = term41) (term56 m n)). Qed.
Lemma lem2394571 (m : int) (n : int) : (term57 m n) = (term57 m n).
Proof. exact (eq_refl (term57 m n)). Qed.
Lemma lem2394572 (m : int) (n : int) : (term51 m n) = (term58 m n).
Proof. exact (MK_COMB (@lem2394571 m n) (@lem2394568 m n)). Qed.
Lemma lem2394574 (m : int) (n : int) : (term46 m n) = (term58 m n).
Proof. exact (TRANS (@lem2394561 m n) (@lem2394572 m n)). Qed.
Lemma lem2394575 (m : int) : (term47 m) = (term59 m).
Proof. exact (fun_ext (fun n : int => @lem2394574 m n)). Qed.
Lemma lem2394576 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2394577 (m : int) : (term48 m) = (term60 m).
Proof. exact (MK_COMB (@lem2394576) (@lem2394575 m)). Qed.
Lemma lem2394578 : term49 = term61.
Proof. exact (fun_ext (fun m : int => @lem2394577 m)). Qed.
Lemma lem2394579 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2394581 : term50 = term62.
Proof. exact (MK_COMB (@lem2394579) (@lem2394578)). Qed.
Lemma lem2394582 (h1 : term10) : term62.
Proof. exact (EQ_MP (@lem2394581) (@lem2394514 h1)). Qed.
Lemma lem2394591 (_29313 : int) (h1 : term10) : term63 _29313.
Proof. exact (@lem2394582 h1 _29313). Qed.
Lemma lem2394592 (_29313 : int) : (term63 _29313) = (term60 _29313).
Proof. exact (eq_refl (term63 _29313)). Qed.
Lemma lem2394593 (_29313 : int) (h1 : term10) : term60 _29313.
Proof. exact (EQ_MP (@lem2394592 _29313) (@lem2394591 _29313 h1)). Qed.
Lemma lem2394594 (_29313 : int) (_29314 : int) (h1 : term10) : term64 _29313 _29314.
Proof. exact (@lem2394593 _29313 h1 _29314). Qed.
Lemma lem2394595 (_29313 : int) (_29314 : int) : (term64 _29313 _29314) = (term58 _29313 _29314).
Proof. exact (eq_refl (term64 _29313 _29314)). Qed.
Lemma lem2394596 (_29313 : int) (_29314 : int) (h1 : term10) : term58 _29313 _29314.
Proof. exact (EQ_MP (@lem2394595 _29313 _29314) (@lem2394594 _29313 _29314 h1)). Qed.
Lemma lem2394597 (_29313 : int) (_29314 : int) (h1 : term10) : term55 _29313 _29314.
Proof. exact (proj2 (@lem2394596 _29313 _29314 h1)). Qed.
Lemma lem2394604 (a : int) (b : int) (h1 : term22 a b) : term65 a b.
Proof. exact (proj2 (@lem2394544 a b h1)). Qed.
Lemma lem2394616 (_29313 : int) (_29314 : int) (h1 : term10) : term66 _29313 _29314.
Proof. exact (proj1 (@lem2394597 _29313 _29314 h1)). Qed.
Lemma lem2394750 (a : int) (b : int) (h1 : term22 a b) : term23 b.
Proof. exact (proj1 (@lem2394544 a b h1)). Qed.
Lemma lem2394751 (a : int) (b : int) (h1 : term22 a b) : term67 b.
Proof. exact (fun h0 : b = term41 => @lem2394750 a b h1). Qed.
Lemma lem2394753 (p : Prop) : (term68 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2394754 (b : int) : (term67 b) = (term23 b).
Proof. exact (@lem2394753 (b = term41)). Qed.
Lemma lem2394755 (a : int) (b : int) (h1 : term22 a b) : term23 b.
Proof. exact (EQ_MP (@lem2394754 b) (@lem2394751 a b h1)). Qed.
Lemma lem2394768 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2394769 (_29313 : int) (_29314 : int) : (term69 _29313 _29314) = (term66 _29313 _29314).
Proof. exact (@lem2394768 (_29314 = term41) (term24 _29313 _29314)). Qed.
Lemma lem2394777 (_29313 : int) (_29314 : int) : (term70 _29313 _29314) = (term70 _29313 _29314).
Proof. exact (eq_refl (term70 _29313 _29314)). Qed.
Lemma lem2394778 (_29313 : int) (_29314 : int) : ((term66 _29313 _29314) = (term69 _29313 _29314)) = ((term66 _29313 _29314) = (term66 _29313 _29314)).
Proof. exact (MK_COMB (@lem2394777 _29313 _29314) (@lem2394769 _29313 _29314)). Qed.
Lemma lem2394780 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2394781 (x : Prop) : (x = x) = True.
Proof. exact (@lem2394780 Prop x). Qed.
Lemma lem2394782 (_29313 : int) (_29314 : int) : ((term66 _29313 _29314) = (term66 _29313 _29314)) = True.
Proof. exact (@lem2394781 (term66 _29313 _29314)). Qed.
Lemma lem2394783 (_29313 : int) (_29314 : int) : ((term66 _29313 _29314) = (term69 _29313 _29314)) = True.
Proof. exact (TRANS (@lem2394778 _29313 _29314) (@lem2394782 _29313 _29314)). Qed.
Lemma lem2394784 (_29313 : int) (_29314 : int) : True = ((term66 _29313 _29314) = (term69 _29313 _29314)).
Proof. exact (SYM (@lem2394783 _29313 _29314)). Qed.
Lemma lem2394785 (_29313 : int) (_29314 : int) : (term66 _29313 _29314) = (term69 _29313 _29314).
Proof. exact (EQ_MP (@lem2394784 _29313 _29314) (@lem0)). Qed.
Lemma lem2394786 (_29313 : int) (_29314 : int) (h1 : term10) : term69 _29313 _29314.
Proof. exact (EQ_MP (@lem2394785 _29313 _29314) (@lem2394616 _29313 _29314 h1)). Qed.
Lemma lem2394788 (b : Prop) (a : Prop) : (a \/ b) = (term71 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2394791 (_29313 : int) (_29314 : int) : (term69 _29313 _29314) = (term17 _29313 _29314).
Proof. exact (@lem2394788 (_29314 = term41) (term24 _29313 _29314)). Qed.
Lemma lem2394794 (_29313 : int) (_29314 : int) (h1 : term10) : term17 _29313 _29314.
Proof. exact (EQ_MP (@lem2394791 _29313 _29314) (@lem2394786 _29313 _29314 h1)). Qed.
Lemma lem2394795 (_29313 : int) (b : int) (h1 : term10) : term17 _29313 b.
Proof. exact (@lem2394794 _29313 b h1). Qed.
Lemma lem2394798 (_29313 : int) (a : int) (b : int) (h1 : term10) (h2 : term22 a b) : term24 _29313 b.
Proof. exact (@lem2394795 _29313 b h1 (@lem2394755 a b h2)). Qed.
Lemma lem2394799 (a : int) (b : int) (h1 : term10) (h2 : term22 a b) : term24 a b.
Proof. exact (@lem2394798 a a b h1 h2). Qed.
Lemma lem2394800 (a : int) (b : int) (h1 : term10) (h2 : term22 a b) : term72 a b.
Proof. exact (fun h0 : term65 a b => @lem2394799 a b h1 h2). Qed.
Lemma lem2394802 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2394803 (a : int) (b : int) : (term72 a b) = (term24 a b).
Proof. exact (@lem2394802 (term24 a b)). Qed.
Lemma lem2394804 (a : int) (b : int) (h1 : term10) (h2 : term22 a b) : term24 a b.
Proof. exact (EQ_MP (@lem2394803 a b) (@lem2394800 a b h1 h2)). Qed.
Lemma lem2394807 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2394809 (a : int) (b : int) : (term65 a b) = (term74 a b).
Proof. exact (@lem2394807 (term24 a b)). Qed.
Lemma lem2394812 (a : int) (b : int) (h1 : term22 a b) : term74 a b.
Proof. exact (EQ_MP (@lem2394809 a b) (@lem2394604 a b h1)). Qed.
Lemma lem2394815 (a : int) (b : int) (h1 : term10) (h2 : term22 a b) : False.
Proof. exact (@lem2394812 a b h2 (@lem2394804 a b h1 h2)). Qed.
Lemma lem2394816 (a : int) (b : int) (h1 : term10) (h2 : term22 a b) : term75.
Proof. exact (fun h0 : ~ False => @lem2394815 a b h1 h2). Qed.
Lemma lem2394818 (p : Prop) : (term73 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2394819 : term75 = False.
Proof. exact (@lem2394818 False). Qed.
Lemma lem2394820 (a : int) (b : int) (h1 : term10) (h2 : term22 a b) : False.
Proof. exact (EQ_MP (@lem2394819) (@lem2394816 a b h1 h2)). Qed.
Lemma lem2394821 (a : int) (b : int) (h1 : term10) (h2 : term22 a b) : (term22 a b) = False.
Proof. exact (prop_ext (fun h3 : term22 a b => @lem2394820 a b h1 h2) (fun h3 : False => @lem2394544 a b h2)). Qed.
Lemma lem2394822 (a : int) (b : int) (h1 : term10) (h2 : term22 a b) : False.
Proof. exact (EQ_MP (@lem2394821 a b h1 h2) (@lem2394544 a b h2)). Qed.
Lemma lem2394823 (a : int) (h1 : term10) (h2 : term33 a) : False.
Proof. exact (ex_elim (@lem2394443 a h2) (fun b : int => fun h0 : term32 a b => @lem2394822 a b h1 h0)). Qed.
Lemma lem2394824 (h1 : term10) (h2 : term3) : False.
Proof. exact (ex_elim (@lem2394362 h2) (fun a : int => fun h0 : term38 a => @lem2394823 a h1 h0)). Qed.
Lemma lem2394825 (h1 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem2394824 h0 h1). Qed.
Lemma lem2394826 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem2394827 (h1 : term3) : term9.
Proof. exact (EQ_MP (@lem2394826) (@lem2394825 h1)). Qed.
Lemma lem2394828 : term12.
Proof. exact (fun h0 : term3 => @lem2394827 h0). Qed.
Lemma lem2394829 : term4.
Proof. exact (EQ_MP (@lem2394276) (@lem2394828)). Qed.
Lemma lem2394831 : term4.
Proof. exact (@lem2394160 (@lem2394829)). Qed.
Lemma lem2394832 (h1 : term3) : term8.
Proof. exact (@lem2394831 (@lem2394145 h1)). Qed.
Lemma lem2394833 (h1 : term3) : False.
Proof. exact (@lem2394832 h1 (@lem2389435)). Qed.
Lemma lem2394834 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem2394833 h1) (fun h2 : False => @lem2394145 h1)). Qed.
Lemma lem2394835 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem2394834 h1) (@lem2394145 h1)). Qed.
Lemma lem2394836 : term2.
Proof. exact (fun h0 : term3 => @lem2394835 h0). Qed.
Lemma lem2394837 : term1.
Proof. exact (EQ_MP (@lem2394144) (@lem2394836)). Qed.
