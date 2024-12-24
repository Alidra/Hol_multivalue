Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ODD_ADD_term_abbrevs.
Require Import EVEN_ADD_spec.
Require Import NOT_DEF_spec.
Require Import NOT_EVEN_spec.
Require Import thm32_spec.
Require Import thm37_spec.
Require Import thm43_spec.
Require Import thm69_spec.
Require Import thm98_spec.
Lemma lem126299 (n : nat) (h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (h1). Qed.
Lemma lem126300 (n : nat) (h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (SYM (@lem126299 n h1)). Qed.
Lemma lem126301 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem126302 (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n).
Proof. exact (SYM (@lem126301 n h1)). Qed.
Lemma lem126303 (n : nat) : ((term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n)) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (Coq.Arith.PeanoNat.Nat.Odd n) => @lem126300 n h1) (fun h1 : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n) => @lem126302 n h1)). Qed.
Lemma lem126304 : term1 = term2.
Proof. exact (fun_ext (fun n : nat => @lem126303 n)). Qed.
Lemma lem126305 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem126306 : term3 = term4.
Proof. exact (MK_COMB (@lem126305) (@lem126304)). Qed.
Lemma lem126307 : term4.
Proof. exact (EQ_MP (@lem126306) (@lem124715)). Qed.
Lemma lem126308 (m : nat) : term5 m.
Proof. exact (@lem125496 m). Qed.
Lemma lem126309 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem126310 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem126309 m) (@lem126308 m)). Qed.
Lemma lem126311 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem126310 m n). Qed.
Lemma lem126312 (m : nat) (n : nat) : (term7 m n) = ((term8 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem126314 (n : nat) : term9 n.
Proof. exact (@lem126307 n). Qed.
Lemma lem126315 (n : nat) : (term9 n) = ((Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n)).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem126320 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem126315 n) (@lem126314 n)). Qed.
Lemma lem126321 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (@lem126320 (Nat.add m n)). Qed.
Lemma lem126323 (m : nat) (n : nat) : (term8 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (EQ_MP (@lem126312 m n) (@lem126311 m n)). Qed.
Lemma lem126326 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem126327 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (MK_COMB (@lem126326) (@lem126323 m n)). Qed.
Lemma lem126328 (m : nat) (n : nat) : (term10 m n) = (term12 m n).
Proof. exact (TRANS (@lem126321 m n) (@lem126327 m n)). Qed.
Lemma lem126329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem126330 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem126329) (@lem126328 m n)). Qed.
Lemma lem126334 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem126315 n) (@lem126314 n)). Qed.
Lemma lem126335 (m : nat) : (Coq.Arith.PeanoNat.Nat.Odd m) = (term0 m).
Proof. exact (@lem126334 m). Qed.
Lemma lem126336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem126337 (m : nat) : (term15 m) = (term16 m).
Proof. exact (MK_COMB (@lem126336) (@lem126335 m)). Qed.
Lemma lem126339 (n : nat) : (Coq.Arith.PeanoNat.Nat.Odd n) = (term0 n).
Proof. exact (EQ_MP (@lem126315 n) (@lem126314 n)). Qed.
Lemma lem126340 (m : nat) (n : nat) : ((Coq.Arith.PeanoNat.Nat.Odd m) = (Coq.Arith.PeanoNat.Nat.Odd n)) = ((term0 m) = (term0 n)).
Proof. exact (MK_COMB (@lem126337 m) (@lem126339 n)). Qed.
Lemma lem126343 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem126344 (m : nat) (n : nat) : (term17 m n) = (term18 m n).
Proof. exact (MK_COMB (@lem126343) (@lem126340 m n)). Qed.
Lemma lem126345 (m : nat) (n : nat) : ((term10 m n) = (term17 m n)) = ((term12 m n) = (term18 m n)).
Proof. exact (MK_COMB (@lem126330 m n) (@lem126344 m n)). Qed.
Lemma lem126348 (m : nat) (n : nat) : ((term12 m n) = (term18 m n)) = ((term10 m n) = (term17 m n)).
Proof. exact (SYM (@lem126345 m n)). Qed.
Lemma lem127297 (m : nat) (n : nat) (h1 : term12 m n) : term12 m n.
Proof. exact (h1). Qed.
Lemma lem127298 (m : nat) (n : nat) (h1 : (term0 m) = (term0 n)) : (term0 m) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem127299 (n : nat) (m : nat) : term19 n m.
Proof. exact (@lem43 (term0 n) (term0 m)). Qed.
Lemma lem127301 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem37 (term0 m) (term0 n)). Qed.
Lemma lem127304 (m : nat) (n : nat) (h1 : (term0 m) = (term0 n)) : term21 n m.
Proof. exact (@lem127299 n m (@lem127298 m n h1)). Qed.
Lemma lem127305 (m : nat) (n : nat) (h1 : (term0 m) = (term0 n)) : term21 m n.
Proof. exact (@lem127301 m n (@lem127298 m n h1)). Qed.
Lemma lem127306 (n : nat) (m : nat) (h1 : term21 n m) : term21 n m.
Proof. exact (h1). Qed.
Lemma lem127307 (m : nat) (n : nat) (h1 : term21 m n) : term21 m n.
Proof. exact (h1). Qed.
Lemma lem127308 (m : nat) (n : nat) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (eq_refl ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))). Qed.
Lemma lem127309 (m : nat) (n : nat) : (term12 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem56) (@lem127308 m n)). Qed.
Lemma lem127310 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem127311 (m : nat) (n : nat) : (term14 m n) = (term14 m n).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem127312 (m : nat) (n : nat) : ((term12 m n) = (term22 m n)) = ((term12 m n) = (term23 m n)).
Proof. exact (MK_COMB (@lem127311 m n) (@lem127310 m n)). Qed.
Lemma lem127313 (m : nat) (n : nat) : (term12 m n) = (term23 m n).
Proof. exact (EQ_MP (@lem127312 m n) (@lem127309 m n)). Qed.
Lemma lem127314 (m : nat) (n : nat) (h1 : term12 m n) : term23 m n.
Proof. exact (EQ_MP (@lem127313 m n) (@lem127297 m n h1)). Qed.
Lemma lem127315 (m : nat) (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (h1). Qed.
Lemma lem127316 (m : nat) (n : nat) (h1 : term12 m n) (h2 : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) : False.
Proof. exact (@lem127314 m n h1 (@lem127315 m n h2)). Qed.
Lemma lem127317 (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (h1). Qed.
Lemma lem127539 (n : nat) (h1 : term0 n) : term0 n.
Proof. exact (h1). Qed.
Lemma lem127540 (n : nat) (m : nat) (h1 : term0 n) (h2 : term21 n m) : term0 m.
Proof. exact (@lem127306 n m h2 (@lem127539 n h1)). Qed.
Lemma lem127541 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem127542 (m : nat) (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (h1). Qed.
Lemma lem127543 (m : nat) (n : nat) (h1 : term12 m n) (h2 : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) : False.
Proof. exact (@lem127314 m n h1 (@lem127542 m n h2)). Qed.
Lemma lem127545 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : term24 m n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even m => @lem127541 n h1). Qed.
Lemma lem127547 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) : term24 n m.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem127317 m h1). Qed.
Lemma lem127548 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : Coq.Arith.PeanoNat.Nat.Even n) : term25 n m.
Proof. exact (conj (@lem127545 m n h2) (@lem127547 n m h1)). Qed.
Lemma lem127549 (m : nat) (n : nat) : (term25 n m) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (@lem32 (Coq.Arith.PeanoNat.Nat.Even m) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem127550 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : Coq.Arith.PeanoNat.Nat.Even n) : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem127549 m n) (@lem127548 m n h1 h2)). Qed.
Lemma lem127551 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : Coq.Arith.PeanoNat.Nat.Even n) (h3 : term12 m n) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) = False.
Proof. exact (prop_ext (fun h4 : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n) => @lem127543 m n h3 h4) (fun h4 : False => @lem127550 m n h1 h2)). Qed.
Lemma lem127552 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : Coq.Arith.PeanoNat.Nat.Even n) (h3 : term12 m n) : False.
Proof. exact (EQ_MP (@lem127551 m n h1 h2 h3) (@lem127550 m n h1 h2)). Qed.
Lemma lem127553 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term12 m n) : term26 n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem127552 m n h1 h0 h2). Qed.
Lemma lem127554 (n : nat) : (term26 n) = (term0 n).
Proof. exact (@lem69 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem127555 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term12 m n) : term0 n.
Proof. exact (EQ_MP (@lem127554 n) (@lem127553 m n h1 h2)). Qed.
Lemma lem127556 (m : nat) : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem127557 (m : nat) : (term0 m) = (term27 m).
Proof. exact (MK_COMB (@lem56) (@lem127556 m)). Qed.
Lemma lem127558 (m : nat) : (term27 m) = (term26 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem127559 (m : nat) : (term16 m) = (term16 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem127560 (m : nat) : ((term0 m) = (term27 m)) = ((term0 m) = (term26 m)).
Proof. exact (MK_COMB (@lem127559 m) (@lem127558 m)). Qed.
Lemma lem127561 (m : nat) : (term0 m) = (term26 m).
Proof. exact (EQ_MP (@lem127560 m) (@lem127557 m)). Qed.
Lemma lem127562 (n : nat) (m : nat) (h1 : term0 n) (h2 : term21 n m) : term26 m.
Proof. exact (EQ_MP (@lem127561 m) (@lem127540 n m h1 h2)). Qed.
Lemma lem127563 (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (h1). Qed.
Lemma lem127564 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term0 n) (h3 : term21 n m) : False.
Proof. exact (@lem127562 n m h2 h3 (@lem127563 m h1)). Qed.
Lemma lem127565 (n : nat) (h1 : False) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (@lem98 (Coq.Arith.PeanoNat.Nat.Even n) h1). Qed.
Lemma lem127566 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term0 n) (h3 : term21 n m) : False = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (prop_ext (fun h4 : False => @lem127565 n h4) (fun h4 : Coq.Arith.PeanoNat.Nat.Even n => @lem127564 n m h1 h2 h3)). Qed.
Lemma lem127567 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term0 n) (h3 : term21 n m) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (EQ_MP (@lem127566 n m h1 h2 h3) (@lem127564 n m h1 h2 h3)). Qed.
Lemma lem127568 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term0 n) (h3 : term21 n m) : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (prop_ext (fun h4 : Coq.Arith.PeanoNat.Nat.Even m => @lem127567 n m h1 h2 h3) (fun h4 : Coq.Arith.PeanoNat.Nat.Even n => @lem127317 m h1)). Qed.
Lemma lem127569 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term0 n) (h3 : term21 n m) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (EQ_MP (@lem127568 n m h1 h2 h3) (@lem127317 m h1)). Qed.
Lemma lem127570 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term12 m n) (h3 : term21 n m) : (term0 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (prop_ext (fun h4 : term0 n => @lem127569 n m h1 h4 h3) (fun h4 : Coq.Arith.PeanoNat.Nat.Even n => @lem127555 m n h1 h2)). Qed.
Lemma lem127571 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term12 m n) (h3 : term21 n m) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (EQ_MP (@lem127570 n m h1 h2 h3) (@lem127555 m n h1 h2)). Qed.
Lemma lem127572 (n : nat) (m : nat) (h1 : term12 m n) (h2 : term21 n m) : term24 m n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even m => @lem127571 n m h0 h1 h2). Qed.
Lemma lem127573 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem127644 (m : nat) (h1 : term0 m) : term0 m.
Proof. exact (h1). Qed.
Lemma lem127645 (m : nat) (n : nat) (h1 : term0 m) (h2 : term21 m n) : term0 n.
Proof. exact (@lem127307 m n h2 (@lem127644 m h1)). Qed.
Lemma lem127646 (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (h1). Qed.
Lemma lem127647 (m : nat) (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (h1). Qed.
Lemma lem127648 (m : nat) (n : nat) (h1 : term12 m n) (h2 : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) : False.
Proof. exact (@lem127314 m n h1 (@lem127647 m n h2)). Qed.
Lemma lem127650 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : term24 m n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even m => @lem127573 n h1). Qed.
Lemma lem127652 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) : term24 n m.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem127646 m h1). Qed.
Lemma lem127653 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : Coq.Arith.PeanoNat.Nat.Even n) : term25 n m.
Proof. exact (conj (@lem127650 m n h2) (@lem127652 n m h1)). Qed.
Lemma lem127654 (m : nat) (n : nat) : (term25 n m) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (@lem32 (Coq.Arith.PeanoNat.Nat.Even m) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem127655 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : Coq.Arith.PeanoNat.Nat.Even n) : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem127654 m n) (@lem127653 m n h1 h2)). Qed.
Lemma lem127656 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : Coq.Arith.PeanoNat.Nat.Even n) (h3 : term12 m n) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) = False.
Proof. exact (prop_ext (fun h4 : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n) => @lem127648 m n h3 h4) (fun h4 : False => @lem127655 m n h1 h2)). Qed.
Lemma lem127657 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : Coq.Arith.PeanoNat.Nat.Even n) (h3 : term12 m n) : False.
Proof. exact (EQ_MP (@lem127656 m n h1 h2 h3) (@lem127655 m n h1 h2)). Qed.
Lemma lem127658 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term12 m n) : term26 m.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even m => @lem127657 m n h0 h1 h2). Qed.
Lemma lem127659 (m : nat) : (term26 m) = (term0 m).
Proof. exact (@lem69 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem127660 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term12 m n) : term0 m.
Proof. exact (EQ_MP (@lem127659 m) (@lem127658 m n h1 h2)). Qed.
Lemma lem127661 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem127662 (n : nat) : (term0 n) = (term27 n).
Proof. exact (MK_COMB (@lem56) (@lem127661 n)). Qed.
Lemma lem127663 (n : nat) : (term27 n) = (term26 n).
Proof. exact (eq_refl (term27 n)). Qed.
Lemma lem127664 (n : nat) : (term16 n) = (term16 n).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem127665 (n : nat) : ((term0 n) = (term27 n)) = ((term0 n) = (term26 n)).
Proof. exact (MK_COMB (@lem127664 n) (@lem127663 n)). Qed.
Lemma lem127666 (n : nat) : (term0 n) = (term26 n).
Proof. exact (EQ_MP (@lem127665 n) (@lem127662 n)). Qed.
Lemma lem127667 (m : nat) (n : nat) (h1 : term0 m) (h2 : term21 m n) : term26 n.
Proof. exact (EQ_MP (@lem127666 n) (@lem127645 m n h1 h2)). Qed.
Lemma lem127668 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem127669 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term0 m) (h3 : term21 m n) : False.
Proof. exact (@lem127667 m n h2 h3 (@lem127668 n h1)). Qed.
Lemma lem127670 (m : nat) (h1 : False) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (@lem98 (Coq.Arith.PeanoNat.Nat.Even m) h1). Qed.
Lemma lem127671 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term0 m) (h3 : term21 m n) : False = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (prop_ext (fun h4 : False => @lem127670 m h4) (fun h4 : Coq.Arith.PeanoNat.Nat.Even m => @lem127669 m n h1 h2 h3)). Qed.
Lemma lem127672 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term0 m) (h3 : term21 m n) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (EQ_MP (@lem127671 m n h1 h2 h3) (@lem127669 m n h1 h2 h3)). Qed.
Lemma lem127673 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term0 m) (h3 : term21 m n) : (Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (prop_ext (fun h4 : Coq.Arith.PeanoNat.Nat.Even n => @lem127672 m n h1 h2 h3) (fun h4 : Coq.Arith.PeanoNat.Nat.Even m => @lem127573 n h1)). Qed.
Lemma lem127674 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term0 m) (h3 : term21 m n) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (EQ_MP (@lem127673 m n h1 h2 h3) (@lem127573 n h1)). Qed.
Lemma lem127675 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term12 m n) (h3 : term21 m n) : (term0 m) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (prop_ext (fun h4 : term0 m => @lem127674 m n h1 h4 h3) (fun h4 : Coq.Arith.PeanoNat.Nat.Even m => @lem127660 m n h1 h2)). Qed.
Lemma lem127676 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term12 m n) (h3 : term21 m n) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (EQ_MP (@lem127675 m n h1 h2 h3) (@lem127660 m n h1 h2)). Qed.
Lemma lem127677 (m : nat) (n : nat) (h1 : term12 m n) (h2 : term21 m n) : term24 n m.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem127676 m n h0 h1 h2). Qed.
Lemma lem127678 (n : nat) (m : nat) (h1 : term12 m n) (h2 : term21 m n) (h3 : term21 n m) : term25 n m.
Proof. exact (conj (@lem127572 n m h1 h3) (@lem127677 m n h1 h2)). Qed.
Lemma lem127679 (m : nat) (n : nat) : (term25 n m) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (@lem32 (Coq.Arith.PeanoNat.Nat.Even m) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem127680 (n : nat) (m : nat) (h1 : term12 m n) (h2 : term21 m n) (h3 : term21 n m) : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem127679 m n) (@lem127678 n m h1 h2 h3)). Qed.
Lemma lem127681 (n : nat) (m : nat) (h1 : term12 m n) (h2 : term21 m n) (h3 : term21 n m) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) = False.
Proof. exact (prop_ext (fun h4 : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n) => @lem127316 m n h1 h4) (fun h4 : False => @lem127680 n m h1 h2 h3)). Qed.
Lemma lem127682 (n : nat) (m : nat) (h1 : term12 m n) (h2 : term21 m n) (h3 : term21 n m) : False.
Proof. exact (EQ_MP (@lem127681 n m h1 h2 h3) (@lem127680 n m h1 h2 h3)). Qed.
Lemma lem127683 (n : nat) (m : nat) (h1 : term12 m n) (h2 : term21 n m) : term28 m n.
Proof. exact (fun h0 : term21 m n => @lem127682 n m h1 h0 h2). Qed.
Lemma lem127684 (m : nat) (n : nat) (h1 : term12 m n) : term29 m n.
Proof. exact (fun h0 : term21 n m => @lem127683 n m h1 h0). Qed.
Lemma lem127685 (m : nat) (n : nat) (h1 : term12 m n) (h2 : (term0 m) = (term0 n)) : term28 m n.
Proof. exact (@lem127684 m n h1 (@lem127304 m n h2)). Qed.
Lemma lem127686 (m : nat) (n : nat) (h1 : term12 m n) (h2 : (term0 m) = (term0 n)) : False.
Proof. exact (@lem127685 m n h1 h2 (@lem127305 m n h2)). Qed.
Lemma lem127687 (m : nat) (n : nat) (h1 : term12 m n) : term30 m n.
Proof. exact (fun h0 : (term0 m) = (term0 n) => @lem127686 m n h1 h0). Qed.
Lemma lem127688 (m : nat) (n : nat) : (term30 m n) = (term18 m n).
Proof. exact (@lem69 ((term0 m) = (term0 n))). Qed.
Lemma lem127689 (m : nat) (n : nat) (h1 : term12 m n) : term18 m n.
Proof. exact (EQ_MP (@lem127688 m n) (@lem127687 m n h1)). Qed.
Lemma lem127690 (m : nat) (n : nat) : term31 m n.
Proof. exact (fun h0 : term12 m n => @lem127689 m n h0). Qed.
Lemma lem127691 (m : nat) (n : nat) (h1 : term18 m n) : term18 m n.
Proof. exact (h1). Qed.
Lemma lem127692 (m : nat) (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (h1). Qed.
Lemma lem127693 (n : nat) (m : nat) : term32 n m.
Proof. exact (@lem43 (Coq.Arith.PeanoNat.Nat.Even n) (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem127695 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem37 (Coq.Arith.PeanoNat.Nat.Even m) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem127698 (m : nat) (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) : term24 n m.
Proof. exact (@lem127693 n m (@lem127692 m n h1)). Qed.
Lemma lem127699 (m : nat) (n : nat) (h1 : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) : term24 m n.
Proof. exact (@lem127695 m n (@lem127692 m n h1)). Qed.
Lemma lem127700 (n : nat) (m : nat) (h1 : term24 n m) : term24 n m.
Proof. exact (h1). Qed.
Lemma lem127701 (m : nat) (n : nat) (h1 : term24 m n) : term24 m n.
Proof. exact (h1). Qed.
Lemma lem127702 (m : nat) (n : nat) : ((term0 m) = (term0 n)) = ((term0 m) = (term0 n)).
Proof. exact (eq_refl ((term0 m) = (term0 n))). Qed.
Lemma lem127703 (m : nat) (n : nat) : (term18 m n) = (term34 m n).
Proof. exact (MK_COMB (@lem56) (@lem127702 m n)). Qed.
Lemma lem127704 (m : nat) (n : nat) : (term34 m n) = (term30 m n).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem127705 (m : nat) (n : nat) : (term35 m n) = (term35 m n).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem127706 (m : nat) (n : nat) : ((term18 m n) = (term34 m n)) = ((term18 m n) = (term30 m n)).
Proof. exact (MK_COMB (@lem127705 m n) (@lem127704 m n)). Qed.
Lemma lem127707 (m : nat) (n : nat) : (term18 m n) = (term30 m n).
Proof. exact (EQ_MP (@lem127706 m n) (@lem127703 m n)). Qed.
Lemma lem127708 (m : nat) (n : nat) (h1 : term18 m n) : term30 m n.
Proof. exact (EQ_MP (@lem127707 m n) (@lem127691 m n h1)). Qed.
Lemma lem127709 (m : nat) (n : nat) (h1 : (term0 m) = (term0 n)) : (term0 m) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem127710 (m : nat) (n : nat) (h1 : term18 m n) (h2 : (term0 m) = (term0 n)) : False.
Proof. exact (@lem127708 m n h1 (@lem127709 m n h2)). Qed.
Lemma lem127711 (m : nat) (h1 : term0 m) : term0 m.
Proof. exact (h1). Qed.
Lemma lem127712 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem127713 (m : nat) : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem127714 (m : nat) : (term0 m) = (term27 m).
Proof. exact (MK_COMB (@lem56) (@lem127713 m)). Qed.
Lemma lem127715 (m : nat) : (term27 m) = (term26 m).
Proof. exact (eq_refl (term27 m)). Qed.
Lemma lem127716 (m : nat) : (term16 m) = (term16 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem127717 (m : nat) : ((term0 m) = (term27 m)) = ((term0 m) = (term26 m)).
Proof. exact (MK_COMB (@lem127716 m) (@lem127715 m)). Qed.
Lemma lem127718 (m : nat) : (term0 m) = (term26 m).
Proof. exact (EQ_MP (@lem127717 m) (@lem127714 m)). Qed.
Lemma lem127719 (m : nat) (h1 : term0 m) : term26 m.
Proof. exact (EQ_MP (@lem127718 m) (@lem127711 m h1)). Qed.
Lemma lem127720 (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (h1). Qed.
Lemma lem127721 (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term0 m) : False.
Proof. exact (@lem127719 m h2 (@lem127720 m h1)). Qed.
Lemma lem127785 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem127786 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term24 n m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (@lem127700 n m h2 (@lem127785 n h1)). Qed.
Lemma lem127787 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term24 n m) : (Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (prop_ext (fun h3 : Coq.Arith.PeanoNat.Nat.Even n => @lem127786 n m h1 h2) (fun h3 : Coq.Arith.PeanoNat.Nat.Even m => @lem127712 n h1)). Qed.
Lemma lem127788 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term24 n m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (EQ_MP (@lem127787 n m h1 h2) (@lem127712 n h1)). Qed.
Lemma lem127789 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term0 m) (h3 : term24 n m) : (Coq.Arith.PeanoNat.Nat.Even m) = False.
Proof. exact (prop_ext (fun h4 : Coq.Arith.PeanoNat.Nat.Even m => @lem127721 m h4 h2) (fun h4 : False => @lem127788 n m h1 h3)). Qed.
Lemma lem127790 (n : nat) (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term0 m) (h3 : term24 n m) : False.
Proof. exact (EQ_MP (@lem127789 n m h1 h2 h3) (@lem127788 n m h1 h3)). Qed.
Lemma lem127791 (n : nat) (m : nat) (h1 : term0 m) (h2 : term24 n m) : term26 n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem127790 n m h0 h1 h2). Qed.
Lemma lem127792 (n : nat) : (term26 n) = (term0 n).
Proof. exact (@lem69 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem127793 (n : nat) (m : nat) (h1 : term0 m) (h2 : term24 n m) : term0 n.
Proof. exact (EQ_MP (@lem127792 n) (@lem127791 n m h1 h2)). Qed.
Lemma lem127794 (n : nat) (m : nat) (h1 : term24 n m) : term21 m n.
Proof. exact (fun h0 : term0 m => @lem127793 n m h0 h1). Qed.
Lemma lem127795 (n : nat) (h1 : term0 n) : term0 n.
Proof. exact (h1). Qed.
Lemma lem127796 (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (h1). Qed.
Lemma lem127797 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem127798 (n : nat) : (term0 n) = (term27 n).
Proof. exact (MK_COMB (@lem56) (@lem127797 n)). Qed.
Lemma lem127799 (n : nat) : (term27 n) = (term26 n).
Proof. exact (eq_refl (term27 n)). Qed.
Lemma lem127800 (n : nat) : (term16 n) = (term16 n).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem127801 (n : nat) : ((term0 n) = (term27 n)) = ((term0 n) = (term26 n)).
Proof. exact (MK_COMB (@lem127800 n) (@lem127799 n)). Qed.
Lemma lem127802 (n : nat) : (term0 n) = (term26 n).
Proof. exact (EQ_MP (@lem127801 n) (@lem127798 n)). Qed.
Lemma lem127803 (n : nat) (h1 : term0 n) : term26 n.
Proof. exact (EQ_MP (@lem127802 n) (@lem127795 n h1)). Qed.
Lemma lem127804 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem127805 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) (h2 : term0 n) : False.
Proof. exact (@lem127803 n h2 (@lem127804 n h1)). Qed.
Lemma lem127859 (m : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (h1). Qed.
Lemma lem127860 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term24 m n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (@lem127701 m n h2 (@lem127859 m h1)). Qed.
Lemma lem127861 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term24 m n) : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (prop_ext (fun h3 : Coq.Arith.PeanoNat.Nat.Even m => @lem127860 m n h1 h2) (fun h3 : Coq.Arith.PeanoNat.Nat.Even n => @lem127796 m h1)). Qed.
Lemma lem127862 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term24 m n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (EQ_MP (@lem127861 m n h1 h2) (@lem127796 m h1)). Qed.
Lemma lem127863 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term0 n) (h3 : term24 m n) : (Coq.Arith.PeanoNat.Nat.Even n) = False.
Proof. exact (prop_ext (fun h4 : Coq.Arith.PeanoNat.Nat.Even n => @lem127805 n h4 h2) (fun h4 : False => @lem127862 m n h1 h3)). Qed.
Lemma lem127864 (m : nat) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even m) (h2 : term0 n) (h3 : term24 m n) : False.
Proof. exact (EQ_MP (@lem127863 m n h1 h2 h3) (@lem127862 m n h1 h3)). Qed.
Lemma lem127865 (m : nat) (n : nat) (h1 : term0 n) (h2 : term24 m n) : term26 m.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even m => @lem127864 m n h0 h1 h2). Qed.
Lemma lem127866 (m : nat) : (term26 m) = (term0 m).
Proof. exact (@lem69 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem127867 (m : nat) (n : nat) (h1 : term0 n) (h2 : term24 m n) : term0 m.
Proof. exact (EQ_MP (@lem127866 m) (@lem127865 m n h1 h2)). Qed.
Lemma lem127868 (m : nat) (n : nat) (h1 : term24 m n) : term21 n m.
Proof. exact (fun h0 : term0 n => @lem127867 m n h0 h1). Qed.
Lemma lem127869 (n : nat) (m : nat) (h1 : term24 m n) (h2 : term24 n m) : term36 n m.
Proof. exact (conj (@lem127794 n m h2) (@lem127868 m n h1)). Qed.
Lemma lem127870 (m : nat) (n : nat) : (term36 n m) = ((term0 m) = (term0 n)).
Proof. exact (@lem32 (term0 m) (term0 n)). Qed.
Lemma lem127871 (n : nat) (m : nat) (h1 : term24 m n) (h2 : term24 n m) : (term0 m) = (term0 n).
Proof. exact (EQ_MP (@lem127870 m n) (@lem127869 n m h1 h2)). Qed.
Lemma lem127872 (n : nat) (m : nat) (h1 : term18 m n) (h2 : term24 m n) (h3 : term24 n m) : ((term0 m) = (term0 n)) = False.
Proof. exact (prop_ext (fun h4 : (term0 m) = (term0 n) => @lem127710 m n h1 h4) (fun h4 : False => @lem127871 n m h2 h3)). Qed.
Lemma lem127873 (n : nat) (m : nat) (h1 : term18 m n) (h2 : term24 m n) (h3 : term24 n m) : False.
Proof. exact (EQ_MP (@lem127872 n m h1 h2 h3) (@lem127871 n m h2 h3)). Qed.
Lemma lem127874 (n : nat) (m : nat) (h1 : term18 m n) (h2 : term24 n m) : term37 m n.
Proof. exact (fun h0 : term24 m n => @lem127873 n m h1 h0 h2). Qed.
Lemma lem127875 (m : nat) (n : nat) (h1 : term18 m n) : term38 m n.
Proof. exact (fun h0 : term24 n m => @lem127874 n m h1 h0). Qed.
Lemma lem127876 (m : nat) (n : nat) (h1 : term18 m n) (h2 : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) : term37 m n.
Proof. exact (@lem127875 m n h1 (@lem127698 m n h2)). Qed.
Lemma lem127877 (m : nat) (n : nat) (h1 : term18 m n) (h2 : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) : False.
Proof. exact (@lem127876 m n h1 h2 (@lem127699 m n h2)). Qed.
Lemma lem127878 (m : nat) (n : nat) (h1 : term18 m n) : term23 m n.
Proof. exact (fun h0 : (Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n) => @lem127877 m n h1 h0). Qed.
Lemma lem127879 (m : nat) (n : nat) : (term23 m n) = (term12 m n).
Proof. exact (@lem69 ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))). Qed.
Lemma lem127880 (m : nat) (n : nat) (h1 : term18 m n) : term12 m n.
Proof. exact (EQ_MP (@lem127879 m n) (@lem127878 m n h1)). Qed.
Lemma lem127881 (m : nat) (n : nat) : term39 m n.
Proof. exact (fun h0 : term18 m n => @lem127880 m n h0). Qed.
Lemma lem127882 (m : nat) (n : nat) : term40 m n.
Proof. exact (conj (@lem127690 m n) (@lem127881 m n)). Qed.
Lemma lem127883 (m : nat) (n : nat) : (term40 m n) = ((term12 m n) = (term18 m n)).
Proof. exact (@lem32 (term12 m n) (term18 m n)). Qed.
Lemma lem127884 (m : nat) (n : nat) : (term12 m n) = (term18 m n).
Proof. exact (EQ_MP (@lem127883 m n) (@lem127882 m n)). Qed.
Lemma lem127885 (m : nat) (n : nat) : (term10 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem126348 m n) (@lem127884 m n)). Qed.
Lemma lem127890 (m : nat) : term41 m.
Proof. exact (fun n : nat => @lem127885 m n). Qed.
Lemma lem127895 : term42.
Proof. exact (fun m : nat => @lem127890 m). Qed.
