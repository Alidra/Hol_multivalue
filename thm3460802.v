Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3460802_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3458986_spec.
Lemma lem3459505 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3459506 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term1 _89711 _89725 P f) = (term2 _89711 _89725 P f).
Proof. exact (@lem3459505 (term1 _89711 _89725 P f)). Qed.
Lemma lem3459507 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term2 _89711 _89725 P f) = (term1 _89711 _89725 P f).
Proof. exact (SYM (@lem3459506 _89711 _89725 P f)). Qed.
Lemma lem3459508 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (h1 : term3 _89711 _89725 P f) : term3 _89711 _89725 P f.
Proof. exact (h1). Qed.
Lemma lem3459511 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (h1 : term2 _89711 _89725 P f) : term2 _89711 _89725 P f.
Proof. exact (h1). Qed.
Lemma lem3459512 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term4 _89711 _89725 P f.
Proof. exact (fun h0 : term2 _89711 _89725 P f => @lem3459511 _89711 _89725 P f h0). Qed.
Lemma lem3459513 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (h1 : term4 _89711 _89725 P f) : term4 _89711 _89725 P f.
Proof. exact (h1). Qed.
Lemma lem3459514 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (h1 : term2 _89711 _89725 P f) : term2 _89711 _89725 P f.
Proof. exact (h1). Qed.
Lemma lem3459515 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (h1 : term2 _89711 _89725 P f) (h2 : term4 _89711 _89725 P f) : term2 _89711 _89725 P f.
Proof. exact (@lem3459513 _89711 _89725 P f h2 (@lem3459514 _89711 _89725 P f h1)). Qed.
Lemma lem3459516 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (h1 : term2 _89711 _89725 P f) : term5 _89711 _89725 P f.
Proof. exact (fun h0 : term4 _89711 _89725 P f => @lem3459515 _89711 _89725 P f h1 h0). Qed.
Lemma lem3459517 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (h1 : term4 _89711 _89725 P f) : term4 _89711 _89725 P f.
Proof. exact (h1). Qed.
Lemma lem3459518 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (h1 : term2 _89711 _89725 P f) (h2 : term4 _89711 _89725 P f) : term2 _89711 _89725 P f.
Proof. exact (@lem3459516 _89711 _89725 P f h1 (@lem3459517 _89711 _89725 P f h2)). Qed.
Lemma lem3459519 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (h1 : term4 _89711 _89725 P f) : term4 _89711 _89725 P f.
Proof. exact (fun h0 : term2 _89711 _89725 P f => @lem3459518 _89711 _89725 P f h0 h1). Qed.
Lemma lem3459520 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term6 _89711 _89725 P f.
Proof. exact (fun h0 : term4 _89711 _89725 P f => @lem3459519 _89711 _89725 P f h0). Qed.
Lemma lem3459523 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term4 _89711 _89725 P f.
Proof. exact (@lem3459520 _89711 _89725 P f (@lem3459512 _89711 _89725 P f)). Qed.
Lemma lem3459524 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term4 _89711 _89725 P f.
Proof. exact (@lem3459523 _89711 _89725 P f). Qed.
Lemma lem3459534 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3459535 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term2 _89711 _89725 P f) = (term7 _89711 _89725 P f).
Proof. exact (@lem3459534 (term3 _89711 _89725 P f)). Qed.
Lemma lem3459537 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3459538 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term7 _89711 _89725 P f) = (term1 _89711 _89725 P f).
Proof. exact (@lem3459537 (term1 _89711 _89725 P f)). Qed.
Lemma lem3459543 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term2 _89711 _89725 P f) = (term1 _89711 _89725 P f).
Proof. exact (TRANS (@lem3459535 _89711 _89725 P f) (@lem3459538 _89711 _89725 P f)). Qed.
Lemma lem3459586 {_89711 _89725 : Type'} (f : type1470 _89711 _89725) : (term9 _89711 _89725 f) = (term10 _89711 _89725 f).
Proof. exact (fun_ext (fun P : _89725 -> Prop => @lem3459543 _89711 _89725 P f)). Qed.
Lemma lem3459587 {_89725 : Type'} : (@all (_89725 -> Prop)) = (@all (_89725 -> Prop)).
Proof. exact (eq_refl (@all (_89725 -> Prop))). Qed.
Lemma lem3459588 {_89711 _89725 : Type'} (f : type1470 _89711 _89725) : (term11 _89711 _89725 f) = (term12 _89711 _89725 f).
Proof. exact (MK_COMB (@lem3459587 _89725) (@lem3459586 _89711 _89725 f)). Qed.
Lemma lem3459593 {_89711 _89725 : Type'} : (term13 _89711 _89725) = (term14 _89711 _89725).
Proof. exact (fun_ext (fun f : type1470 _89711 _89725 => @lem3459588 _89711 _89725 f)). Qed.
Lemma lem3459594 {_89711 _89725 : Type'} : (@all (_89725 -> _89711 -> Prop)) = (@all (_89725 -> _89711 -> Prop)).
Proof. exact (eq_refl (@all (_89725 -> _89711 -> Prop))). Qed.
Lemma lem3459603 {_89711 _89725 : Type'} : (term15 _89711 _89725) = (term16 _89711 _89725).
Proof. exact (MK_COMB (@lem3459594 _89711 _89725) (@lem3459593 _89711 _89725)). Qed.
Lemma lem3459608 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term17 _89711 _89725 P x f x') = (term17 _89711 _89725 P x f x').
Proof. exact (eq_refl (term17 _89711 _89725 P x f x')). Qed.
Lemma lem3459609 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term18 _89711 _89725 P x f) = (term18 _89711 _89725 P x f).
Proof. exact (fun_ext (fun x' : _89725 => @lem3459608 _89711 _89725 P x f x')). Qed.
Lemma lem3459610 {_89725 : Type'} : (@all _89725) = (@all _89725).
Proof. exact (eq_refl (@all _89725)). Qed.
Lemma lem3459611 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term19 _89711 _89725 P x f) = (term19 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3459610 _89725) (@lem3459609 _89711 _89725 P x f)). Qed.
Lemma lem3459612 {_89711 : Type'} (x : _89711) (t : _89711 -> Prop) : (@IN _89711 x t) = (@IN _89711 x t).
Proof. exact (eq_refl (@IN _89711 x t)). Qed.
Lemma lem3459617 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term20 _89711 _89725 P t f x) = (term20 _89711 _89725 P t f x).
Proof. exact (eq_refl (term20 _89711 _89725 P t f x)). Qed.
Lemma lem3459618 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term21 _89711 _89725 P t f) = (term21 _89711 _89725 P t f).
Proof. exact (fun_ext (fun x : _89725 => @lem3459617 _89711 _89725 P t f x)). Qed.
Lemma lem3459619 {_89725 : Type'} : (@ex _89725) = (@ex _89725).
Proof. exact (eq_refl (@ex _89725)). Qed.
Lemma lem3459620 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term22 _89711 _89725 P t f) = (term22 _89711 _89725 P t f).
Proof. exact (MK_COMB (@lem3459619 _89725) (@lem3459618 _89711 _89725 P t f)). Qed.
Lemma lem3459621 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3459622 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term23 _89711 _89725 P t f) = (term23 _89711 _89725 P t f).
Proof. exact (MK_COMB (@lem3459621) (@lem3459620 _89711 _89725 P t f)). Qed.
Lemma lem3459623 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term24 _89711 _89725 P f x t) = (term24 _89711 _89725 P f x t).
Proof. exact (MK_COMB (@lem3459622 _89711 _89725 P t f) (@lem3459612 _89711 x t)). Qed.
Lemma lem3459624 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term25 _89711 _89725 P f x) = (term25 _89711 _89725 P f x).
Proof. exact (fun_ext (fun t : _89711 -> Prop => @lem3459623 _89711 _89725 P f x t)). Qed.
Lemma lem3459625 {_89711 : Type'} : (@all (_89711 -> Prop)) = (@all (_89711 -> Prop)).
Proof. exact (eq_refl (@all (_89711 -> Prop))). Qed.
Lemma lem3459626 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term26 _89711 _89725 P f x) = (term26 _89711 _89725 P f x).
Proof. exact (MK_COMB (@lem3459625 _89711) (@lem3459624 _89711 _89725 P f x)). Qed.
Lemma lem3459627 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3459628 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term27 _89711 _89725 P f x) = (term27 _89711 _89725 P f x).
Proof. exact (MK_COMB (@lem3459627) (@lem3459626 _89711 _89725 P f x)). Qed.
Lemma lem3459629 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : ((term26 _89711 _89725 P f x) = (term19 _89711 _89725 P x f)) = ((term26 _89711 _89725 P f x) = (term19 _89711 _89725 P x f)).
Proof. exact (MK_COMB (@lem3459628 _89711 _89725 P f x) (@lem3459611 _89711 _89725 P x f)). Qed.
Lemma lem3459630 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term28 _89711 _89725 P f) = (term28 _89711 _89725 P f).
Proof. exact (fun_ext (fun x : _89711 => @lem3459629 _89711 _89725 P x f)). Qed.
Lemma lem3459631 {_89711 : Type'} : (@all _89711) = (@all _89711).
Proof. exact (eq_refl (@all _89711)). Qed.
Lemma lem3459632 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term1 _89711 _89725 P f) = (term1 _89711 _89725 P f).
Proof. exact (MK_COMB (@lem3459631 _89711) (@lem3459630 _89711 _89725 P f)). Qed.
Lemma lem3459633 {_89711 _89725 : Type'} (f : type1470 _89711 _89725) : (term10 _89711 _89725 f) = (term10 _89711 _89725 f).
Proof. exact (fun_ext (fun P : _89725 -> Prop => @lem3459632 _89711 _89725 P f)). Qed.
Lemma lem3459634 {_89725 : Type'} : (@all (_89725 -> Prop)) = (@all (_89725 -> Prop)).
Proof. exact (eq_refl (@all (_89725 -> Prop))). Qed.
Lemma lem3459635 {_89711 _89725 : Type'} (f : type1470 _89711 _89725) : (term12 _89711 _89725 f) = (term12 _89711 _89725 f).
Proof. exact (MK_COMB (@lem3459634 _89725) (@lem3459633 _89711 _89725 f)). Qed.
Lemma lem3459636 {_89711 _89725 : Type'} : (term14 _89711 _89725) = (term14 _89711 _89725).
Proof. exact (fun_ext (fun f : type1470 _89711 _89725 => @lem3459635 _89711 _89725 f)). Qed.
Lemma lem3459637 {_89711 _89725 : Type'} : (@all (_89725 -> _89711 -> Prop)) = (@all (_89725 -> _89711 -> Prop)).
Proof. exact (eq_refl (@all (_89725 -> _89711 -> Prop))). Qed.
Lemma lem3459638 {_89711 _89725 : Type'} : (term16 _89711 _89725) = (term16 _89711 _89725).
Proof. exact (MK_COMB (@lem3459637 _89711 _89725) (@lem3459636 _89711 _89725)). Qed.
Lemma lem3459683 {_89711 _89725 : Type'} : (term15 _89711 _89725) = (term16 _89711 _89725).
Proof. exact (TRANS (@lem3459603 _89711 _89725) (@lem3459638 _89711 _89725)). Qed.
Lemma lem3459684 {_89711 _89725 : Type'} : (term16 _89711 _89725) = (term15 _89711 _89725).
Proof. exact (SYM (@lem3459683 _89711 _89725)). Qed.
Lemma lem3459686 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3459687 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : ((term26 _89711 _89725 P f x) = (term19 _89711 _89725 P x f)) = (term29 _89711 _89725 P x f).
Proof. exact (@lem3459686 ((term26 _89711 _89725 P f x) = (term19 _89711 _89725 P x f))). Qed.
Lemma lem3459688 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term29 _89711 _89725 P x f) = ((term26 _89711 _89725 P f x) = (term19 _89711 _89725 P x f)).
Proof. exact (SYM (@lem3459687 _89711 _89725 P x f)). Qed.
Lemma lem3459689 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term30 _89711 _89725 P x f) : term30 _89711 _89725 P x f.
Proof. exact (h1). Qed.
Lemma lem3459698 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term31 _89711 _89725 P t f x) = (term32 _89711 _89725 P t f x).
Proof. exact (@lem17045 (P x) (t = (f x))). Qed.
Lemma lem3459701 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term20 _89711 _89725 P t f x) = (term20 _89711 _89725 P t f x).
Proof. exact (eq_refl (term20 _89711 _89725 P t f x)). Qed.
Lemma lem3459702 {_89725 : Type'} (P : _89725 -> Prop) : (term33 _89725 P) = (term34 _89725 P).
Proof. exact (@lem18394 _89725 P). Qed.
Lemma lem3459703 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term35 _89711 _89725 P t f) = (term36 _89711 _89725 P t f).
Proof. exact (@lem3459702 _89725 (term21 _89711 _89725 P t f)). Qed.
Lemma lem3459704 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term37 _89711 _89725 P t f x) = (term20 _89711 _89725 P t f x).
Proof. exact (eq_refl (term37 _89711 _89725 P t f x)). Qed.
Lemma lem3459705 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3459706 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term38 _89711 _89725 P t f x) = (term31 _89711 _89725 P t f x).
Proof. exact (MK_COMB (@lem3459705) (@lem3459704 _89711 _89725 P t f x)). Qed.
Lemma lem3459707 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term38 _89711 _89725 P t f x) = (term32 _89711 _89725 P t f x).
Proof. exact (TRANS (@lem3459706 _89711 _89725 P t f x) (@lem3459698 _89711 _89725 P t f x)). Qed.
Lemma lem3459708 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term39 _89711 _89725 P t f) = (term40 _89711 _89725 P t f).
Proof. exact (fun_ext (fun x : _89725 => @lem3459707 _89711 _89725 P t f x)). Qed.
Lemma lem3459709 {_89725 : Type'} : (@all _89725) = (@all _89725).
Proof. exact (eq_refl (@all _89725)). Qed.
Lemma lem3459710 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term36 _89711 _89725 P t f) = (term41 _89711 _89725 P t f).
Proof. exact (MK_COMB (@lem3459709 _89725) (@lem3459708 _89711 _89725 P t f)). Qed.
Lemma lem3459711 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term35 _89711 _89725 P t f) = (term41 _89711 _89725 P t f).
Proof. exact (TRANS (@lem3459703 _89711 _89725 P t f) (@lem3459710 _89711 _89725 P t f)). Qed.
Lemma lem3459712 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term21 _89711 _89725 P t f) = (term21 _89711 _89725 P t f).
Proof. exact (fun_ext (fun x : _89725 => @lem3459701 _89711 _89725 P t f x)). Qed.
Lemma lem3459713 {_89725 : Type'} : (@ex _89725) = (@ex _89725).
Proof. exact (eq_refl (@ex _89725)). Qed.
Lemma lem3459714 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term22 _89711 _89725 P t f) = (term22 _89711 _89725 P t f).
Proof. exact (MK_COMB (@lem3459713 _89725) (@lem3459712 _89711 _89725 P t f)). Qed.
Lemma lem3459715 {_89711 : Type'} (x : _89711) (t : _89711 -> Prop) : (term42 _89711 x t) = (term42 _89711 x t).
Proof. exact (eq_refl (term42 _89711 x t)). Qed.
Lemma lem3459716 {_89711 : Type'} (x : _89711) (t : _89711 -> Prop) : (@IN _89711 x t) = (@IN _89711 x t).
Proof. exact (eq_refl (@IN _89711 x t)). Qed.
Lemma lem3459717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3459718 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term43 _89711 _89725 P t f) = (term43 _89711 _89725 P t f).
Proof. exact (MK_COMB (@lem3459717) (@lem3459714 _89711 _89725 P t f)). Qed.
Lemma lem3459719 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term44 _89711 _89725 P f x t) = (term44 _89711 _89725 P f x t).
Proof. exact (MK_COMB (@lem3459718 _89711 _89725 P t f) (@lem3459715 _89711 x t)). Qed.
Lemma lem3459720 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term45 _89711 _89725 P f x t) = (term44 _89711 _89725 P f x t).
Proof. exact (@lem17362 (term22 _89711 _89725 P t f) (@IN _89711 x t)). Qed.
Lemma lem3459721 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term45 _89711 _89725 P f x t) = (term44 _89711 _89725 P f x t).
Proof. exact (TRANS (@lem3459720 _89711 _89725 P f x t) (@lem3459719 _89711 _89725 P f x t)). Qed.
Lemma lem3459722 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3459723 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term46 _89711 _89725 P t f) = (term47 _89711 _89725 P t f).
Proof. exact (MK_COMB (@lem3459722) (@lem3459711 _89711 _89725 P t f)). Qed.
Lemma lem3459724 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term48 _89711 _89725 P f x t) = (term49 _89711 _89725 P f x t).
Proof. exact (MK_COMB (@lem3459723 _89711 _89725 P t f) (@lem3459716 _89711 x t)). Qed.
Lemma lem3459725 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term24 _89711 _89725 P f x t) = (term48 _89711 _89725 P f x t).
Proof. exact (@lem17265 (term22 _89711 _89725 P t f) (@IN _89711 x t)). Qed.
Lemma lem3459726 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term24 _89711 _89725 P f x t) = (term49 _89711 _89725 P f x t).
Proof. exact (TRANS (@lem3459725 _89711 _89725 P f x t) (@lem3459724 _89711 _89725 P f x t)). Qed.
Lemma lem3459727 {_89711 : Type'} (P : type686 _89711) : (term50 _89711 P) = (term51 _89711 P).
Proof. exact (@lem18392 (_89711 -> Prop) P). Qed.
Lemma lem3459728 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term52 _89711 _89725 P f x) = (term53 _89711 _89725 P f x).
Proof. exact (@lem3459727 _89711 (term25 _89711 _89725 P f x)). Qed.
Lemma lem3459729 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term54 _89711 _89725 P f x t) = (term24 _89711 _89725 P f x t).
Proof. exact (eq_refl (term54 _89711 _89725 P f x t)). Qed.
Lemma lem3459730 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3459731 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term55 _89711 _89725 P f x t) = (term45 _89711 _89725 P f x t).
Proof. exact (MK_COMB (@lem3459730) (@lem3459729 _89711 _89725 P f x t)). Qed.
Lemma lem3459732 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term55 _89711 _89725 P f x t) = (term44 _89711 _89725 P f x t).
Proof. exact (TRANS (@lem3459731 _89711 _89725 P f x t) (@lem3459721 _89711 _89725 P f x t)). Qed.
Lemma lem3459733 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term56 _89711 _89725 P f x) = (term57 _89711 _89725 P f x).
Proof. exact (fun_ext (fun t : _89711 -> Prop => @lem3459732 _89711 _89725 P f x t)). Qed.
Lemma lem3459734 {_89711 : Type'} : (@ex (_89711 -> Prop)) = (@ex (_89711 -> Prop)).
Proof. exact (eq_refl (@ex (_89711 -> Prop))). Qed.
Lemma lem3459735 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term53 _89711 _89725 P f x) = (term58 _89711 _89725 P f x).
Proof. exact (MK_COMB (@lem3459734 _89711) (@lem3459733 _89711 _89725 P f x)). Qed.
Lemma lem3459736 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term52 _89711 _89725 P f x) = (term58 _89711 _89725 P f x).
Proof. exact (TRANS (@lem3459728 _89711 _89725 P f x) (@lem3459735 _89711 _89725 P f x)). Qed.
Lemma lem3459737 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term25 _89711 _89725 P f x) = (term59 _89711 _89725 P f x).
Proof. exact (fun_ext (fun t : _89711 -> Prop => @lem3459726 _89711 _89725 P f x t)). Qed.
Lemma lem3459738 {_89711 : Type'} : (@all (_89711 -> Prop)) = (@all (_89711 -> Prop)).
Proof. exact (eq_refl (@all (_89711 -> Prop))). Qed.
Lemma lem3459739 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term26 _89711 _89725 P f x) = (term60 _89711 _89725 P f x).
Proof. exact (MK_COMB (@lem3459738 _89711) (@lem3459737 _89711 _89725 P f x)). Qed.
Lemma lem3459748 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term61 _89711 _89725 P x f x') = (term62 _89711 _89725 P x f x').
Proof. exact (@lem17362 (P x') (term63 _89711 _89725 x f x')). Qed.
Lemma lem3459753 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term17 _89711 _89725 P x f x') = (term64 _89711 _89725 P x f x').
Proof. exact (@lem17265 (P x') (term63 _89711 _89725 x f x')). Qed.
Lemma lem3459754 {_89725 : Type'} (P : _89725 -> Prop) : (term65 _89725 P) = (term66 _89725 P).
Proof. exact (@lem18392 _89725 P). Qed.
Lemma lem3459755 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term67 _89711 _89725 P x f) = (term68 _89711 _89725 P x f).
Proof. exact (@lem3459754 _89725 (term18 _89711 _89725 P x f)). Qed.
Lemma lem3459756 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term69 _89711 _89725 P x f x') = (term17 _89711 _89725 P x f x').
Proof. exact (eq_refl (term69 _89711 _89725 P x f x')). Qed.
Lemma lem3459757 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3459758 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term70 _89711 _89725 P x f x') = (term61 _89711 _89725 P x f x').
Proof. exact (MK_COMB (@lem3459757) (@lem3459756 _89711 _89725 P x f x')). Qed.
Lemma lem3459759 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term70 _89711 _89725 P x f x') = (term62 _89711 _89725 P x f x').
Proof. exact (TRANS (@lem3459758 _89711 _89725 P x f x') (@lem3459748 _89711 _89725 P x f x')). Qed.
Lemma lem3459760 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term71 _89711 _89725 P x f) = (term72 _89711 _89725 P x f).
Proof. exact (fun_ext (fun x' : _89725 => @lem3459759 _89711 _89725 P x f x')). Qed.
Lemma lem3459761 {_89725 : Type'} : (@ex _89725) = (@ex _89725).
Proof. exact (eq_refl (@ex _89725)). Qed.
Lemma lem3459762 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term68 _89711 _89725 P x f) = (term73 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3459761 _89725) (@lem3459760 _89711 _89725 P x f)). Qed.
Lemma lem3459763 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term67 _89711 _89725 P x f) = (term73 _89711 _89725 P x f).
Proof. exact (TRANS (@lem3459755 _89711 _89725 P x f) (@lem3459762 _89711 _89725 P x f)). Qed.
Lemma lem3459764 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term18 _89711 _89725 P x f) = (term74 _89711 _89725 P x f).
Proof. exact (fun_ext (fun x' : _89725 => @lem3459753 _89711 _89725 P x f x')). Qed.
Lemma lem3459765 {_89725 : Type'} : (@all _89725) = (@all _89725).
Proof. exact (eq_refl (@all _89725)). Qed.
Lemma lem3459766 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term19 _89711 _89725 P x f) = (term75 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3459765 _89725) (@lem3459764 _89711 _89725 P x f)). Qed.
Lemma lem3459767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3459768 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term76 _89711 _89725 P f x) = (term77 _89711 _89725 P f x).
Proof. exact (MK_COMB (@lem3459767) (@lem3459736 _89711 _89725 P f x)). Qed.
Lemma lem3459769 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term78 _89711 _89725 P x f) = (term79 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3459768 _89711 _89725 P f x) (@lem3459766 _89711 _89725 P x f)). Qed.
Lemma lem3459770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3459771 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term80 _89711 _89725 P f x) = (term81 _89711 _89725 P f x).
Proof. exact (MK_COMB (@lem3459770) (@lem3459739 _89711 _89725 P f x)). Qed.
Lemma lem3459772 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term82 _89711 _89725 P x f) = (term83 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3459771 _89711 _89725 P f x) (@lem3459763 _89711 _89725 P x f)). Qed.
Lemma lem3459773 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3459774 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term84 _89711 _89725 P x f) = (term85 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3459773) (@lem3459772 _89711 _89725 P x f)). Qed.
Lemma lem3459775 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term86 _89711 _89725 P x f) = (term87 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3459774 _89711 _89725 P x f) (@lem3459769 _89711 _89725 P x f)). Qed.
Lemma lem3459776 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term30 _89711 _89725 P x f) = (term86 _89711 _89725 P x f).
Proof. exact (@lem17646 (term26 _89711 _89725 P f x) (term19 _89711 _89725 P x f)). Qed.
Lemma lem3459777 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term30 _89711 _89725 P x f) = (term87 _89711 _89725 P x f).
Proof. exact (TRANS (@lem3459776 _89711 _89725 P x f) (@lem3459775 _89711 _89725 P x f)). Qed.
Lemma lem3460028 {A : Type'} (P : Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3460029 {_89725 : Type'} (P : Prop) (Q : _89725 -> Prop) : (term88 _89725 P Q) = (term89 _89725 P Q).
Proof. exact (@lem3460028 _89725 P Q). Qed.
Lemma lem3460030 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term90 _89711 _89725 P x f) = (term91 _89711 _89725 P x f).
Proof. exact (@lem3460029 _89725 (term60 _89711 _89725 P f x) (term72 _89711 _89725 P x f)). Qed.
Lemma lem3460031 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term92 _89711 _89725 P x f x') = (term62 _89711 _89725 P x f x').
Proof. exact (eq_refl (term92 _89711 _89725 P x f x')). Qed.
Lemma lem3460032 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term93 _89711 _89725 P x f) = (term72 _89711 _89725 P x f).
Proof. exact (fun_ext (fun x' : _89725 => @lem3460031 _89711 _89725 P x f x')). Qed.
Lemma lem3460033 {_89725 : Type'} : (@ex _89725) = (@ex _89725).
Proof. exact (eq_refl (@ex _89725)). Qed.
Lemma lem3460034 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term94 _89711 _89725 P x f) = (term73 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460033 _89725) (@lem3460032 _89711 _89725 P x f)). Qed.
Lemma lem3460035 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term81 _89711 _89725 P f x) = (term81 _89711 _89725 P f x).
Proof. exact (eq_refl (term81 _89711 _89725 P f x)). Qed.
Lemma lem3460036 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term90 _89711 _89725 P x f) = (term83 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460035 _89711 _89725 P f x) (@lem3460034 _89711 _89725 P x f)). Qed.
Lemma lem3460037 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3460038 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term95 _89711 _89725 P x f) = (term96 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460037) (@lem3460036 _89711 _89725 P x f)). Qed.
Lemma lem3460039 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term92 _89711 _89725 P x f x') = (term62 _89711 _89725 P x f x').
Proof. exact (eq_refl (term92 _89711 _89725 P x f x')). Qed.
Lemma lem3460040 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term81 _89711 _89725 P f x) = (term81 _89711 _89725 P f x).
Proof. exact (eq_refl (term81 _89711 _89725 P f x)). Qed.
Lemma lem3460041 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term97 _89711 _89725 P x f x') = (term98 _89711 _89725 P x f x').
Proof. exact (MK_COMB (@lem3460040 _89711 _89725 P f x) (@lem3460039 _89711 _89725 P x f x')). Qed.
Lemma lem3460042 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term99 _89711 _89725 P x f) = (term100 _89711 _89725 P x f).
Proof. exact (fun_ext (fun x' : _89725 => @lem3460041 _89711 _89725 P x f x')). Qed.
Lemma lem3460043 {_89725 : Type'} : (@ex _89725) = (@ex _89725).
Proof. exact (eq_refl (@ex _89725)). Qed.
Lemma lem3460044 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term91 _89711 _89725 P x f) = (term101 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460043 _89725) (@lem3460042 _89711 _89725 P x f)). Qed.
Lemma lem3460045 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : ((term90 _89711 _89725 P x f) = (term91 _89711 _89725 P x f)) = ((term83 _89711 _89725 P x f) = (term101 _89711 _89725 P x f)).
Proof. exact (MK_COMB (@lem3460038 _89711 _89725 P x f) (@lem3460044 _89711 _89725 P x f)). Qed.
Lemma lem3460046 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term83 _89711 _89725 P x f) = (term101 _89711 _89725 P x f).
Proof. exact (EQ_MP (@lem3460045 _89711 _89725 P x f) (@lem3460030 _89711 _89725 P x f)). Qed.
Lemma lem3460047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3460048 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term85 _89711 _89725 P x f) = (term102 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460047) (@lem3460046 _89711 _89725 P x f)). Qed.
Lemma lem3460050 {A : Type'} (P : A -> Prop) (Q : Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3460051 {_89725 : Type'} (P : _89725 -> Prop) (Q : Prop) : (term103 _89725 P Q) = (term104 _89725 P Q).
Proof. exact (@lem3460050 _89725 P Q). Qed.
Lemma lem3460052 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term105 _89711 _89725 P f x t) = (term106 _89711 _89725 P f x t).
Proof. exact (@lem3460051 _89725 (term21 _89711 _89725 P t f) (term42 _89711 x t)). Qed.
Lemma lem3460053 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term37 _89711 _89725 P t f x) = (term20 _89711 _89725 P t f x).
Proof. exact (eq_refl (term37 _89711 _89725 P t f x)). Qed.
Lemma lem3460054 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term107 _89711 _89725 P t f) = (term21 _89711 _89725 P t f).
Proof. exact (fun_ext (fun x : _89725 => @lem3460053 _89711 _89725 P t f x)). Qed.
Lemma lem3460055 {_89725 : Type'} : (@ex _89725) = (@ex _89725).
Proof. exact (eq_refl (@ex _89725)). Qed.
Lemma lem3460056 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term108 _89711 _89725 P t f) = (term22 _89711 _89725 P t f).
Proof. exact (MK_COMB (@lem3460055 _89725) (@lem3460054 _89711 _89725 P t f)). Qed.
Lemma lem3460057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3460058 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term109 _89711 _89725 P t f) = (term43 _89711 _89725 P t f).
Proof. exact (MK_COMB (@lem3460057) (@lem3460056 _89711 _89725 P t f)). Qed.
Lemma lem3460059 {_89711 : Type'} (x : _89711) (t : _89711 -> Prop) : (term42 _89711 x t) = (term42 _89711 x t).
Proof. exact (eq_refl (term42 _89711 x t)). Qed.
Lemma lem3460060 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term105 _89711 _89725 P f x t) = (term44 _89711 _89725 P f x t).
Proof. exact (MK_COMB (@lem3460058 _89711 _89725 P t f) (@lem3460059 _89711 x t)). Qed.
Lemma lem3460061 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3460062 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term110 _89711 _89725 P f x t) = (term111 _89711 _89725 P f x t).
Proof. exact (MK_COMB (@lem3460061) (@lem3460060 _89711 _89725 P f x t)). Qed.
Lemma lem3460063 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term37 _89711 _89725 P t f x) = (term20 _89711 _89725 P t f x).
Proof. exact (eq_refl (term37 _89711 _89725 P t f x)). Qed.
Lemma lem3460064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3460065 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term112 _89711 _89725 P t f x) = (term113 _89711 _89725 P t f x).
Proof. exact (MK_COMB (@lem3460064) (@lem3460063 _89711 _89725 P t f x)). Qed.
Lemma lem3460066 {_89711 : Type'} (x : _89711) (t : _89711 -> Prop) : (term42 _89711 x t) = (term42 _89711 x t).
Proof. exact (eq_refl (term42 _89711 x t)). Qed.
Lemma lem3460067 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89725) (x' : _89711) (t : _89711 -> Prop) : (term114 _89711 _89725 P f x x' t) = (term115 _89711 _89725 P f x x' t).
Proof. exact (MK_COMB (@lem3460065 _89711 _89725 P t f x) (@lem3460066 _89711 x' t)). Qed.
Lemma lem3460068 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term116 _89711 _89725 P f x t) = (term117 _89711 _89725 P f x t).
Proof. exact (fun_ext (fun x' : _89725 => @lem3460067 _89711 _89725 P f x' x t)). Qed.
Lemma lem3460069 {_89725 : Type'} : (@ex _89725) = (@ex _89725).
Proof. exact (eq_refl (@ex _89725)). Qed.
Lemma lem3460070 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term106 _89711 _89725 P f x t) = (term118 _89711 _89725 P f x t).
Proof. exact (MK_COMB (@lem3460069 _89725) (@lem3460068 _89711 _89725 P f x t)). Qed.
Lemma lem3460071 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : ((term105 _89711 _89725 P f x t) = (term106 _89711 _89725 P f x t)) = ((term44 _89711 _89725 P f x t) = (term118 _89711 _89725 P f x t)).
Proof. exact (MK_COMB (@lem3460062 _89711 _89725 P f x t) (@lem3460070 _89711 _89725 P f x t)). Qed.
Lemma lem3460072 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term44 _89711 _89725 P f x t) = (term118 _89711 _89725 P f x t).
Proof. exact (EQ_MP (@lem3460071 _89711 _89725 P f x t) (@lem3460052 _89711 _89725 P f x t)). Qed.
Lemma lem3460073 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term57 _89711 _89725 P f x) = (term119 _89711 _89725 P f x).
Proof. exact (fun_ext (fun t : _89711 -> Prop => @lem3460072 _89711 _89725 P f x t)). Qed.
Lemma lem3460074 {_89711 : Type'} : (@ex (_89711 -> Prop)) = (@ex (_89711 -> Prop)).
Proof. exact (eq_refl (@ex (_89711 -> Prop))). Qed.
Lemma lem3460075 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term58 _89711 _89725 P f x) = (term120 _89711 _89725 P f x).
Proof. exact (MK_COMB (@lem3460074 _89711) (@lem3460073 _89711 _89725 P f x)). Qed.
Lemma lem3460076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3460077 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term77 _89711 _89725 P f x) = (term121 _89711 _89725 P f x).
Proof. exact (MK_COMB (@lem3460076) (@lem3460075 _89711 _89725 P f x)). Qed.
Lemma lem3460078 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term75 _89711 _89725 P x f) = (term75 _89711 _89725 P x f).
Proof. exact (eq_refl (term75 _89711 _89725 P x f)). Qed.
Lemma lem3460079 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term79 _89711 _89725 P x f) = (term122 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460077 _89711 _89725 P f x) (@lem3460078 _89711 _89725 P x f)). Qed.
Lemma lem3460081 {A : Type'} (P : A -> Prop) (Q : Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3460082 {_89711 : Type'} (P : type686 _89711) (Q : Prop) : (term123 _89711 P Q) = (term124 _89711 P Q).
Proof. exact (@lem3460081 (_89711 -> Prop) P Q). Qed.
Lemma lem3460083 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term125 _89711 _89725 P x f) = (term126 _89711 _89725 P x f).
Proof. exact (@lem3460082 _89711 (term119 _89711 _89725 P f x) (term75 _89711 _89725 P x f)). Qed.
Lemma lem3460084 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term127 _89711 _89725 P f x t) = (term118 _89711 _89725 P f x t).
Proof. exact (eq_refl (term127 _89711 _89725 P f x t)). Qed.
Lemma lem3460085 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term128 _89711 _89725 P f x) = (term119 _89711 _89725 P f x).
Proof. exact (fun_ext (fun t : _89711 -> Prop => @lem3460084 _89711 _89725 P f x t)). Qed.
Lemma lem3460086 {_89711 : Type'} : (@ex (_89711 -> Prop)) = (@ex (_89711 -> Prop)).
Proof. exact (eq_refl (@ex (_89711 -> Prop))). Qed.
Lemma lem3460087 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term129 _89711 _89725 P f x) = (term120 _89711 _89725 P f x).
Proof. exact (MK_COMB (@lem3460086 _89711) (@lem3460085 _89711 _89725 P f x)). Qed.
Lemma lem3460088 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3460089 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term130 _89711 _89725 P f x) = (term121 _89711 _89725 P f x).
Proof. exact (MK_COMB (@lem3460088) (@lem3460087 _89711 _89725 P f x)). Qed.
Lemma lem3460090 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term75 _89711 _89725 P x f) = (term75 _89711 _89725 P x f).
Proof. exact (eq_refl (term75 _89711 _89725 P x f)). Qed.
Lemma lem3460091 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term125 _89711 _89725 P x f) = (term122 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460089 _89711 _89725 P f x) (@lem3460090 _89711 _89725 P x f)). Qed.
Lemma lem3460092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3460093 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term131 _89711 _89725 P x f) = (term132 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460092) (@lem3460091 _89711 _89725 P x f)). Qed.
Lemma lem3460094 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term127 _89711 _89725 P f x t) = (term118 _89711 _89725 P f x t).
Proof. exact (eq_refl (term127 _89711 _89725 P f x t)). Qed.
Lemma lem3460095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3460096 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term133 _89711 _89725 P f x t) = (term134 _89711 _89725 P f x t).
Proof. exact (MK_COMB (@lem3460095) (@lem3460094 _89711 _89725 P f x t)). Qed.
Lemma lem3460097 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term75 _89711 _89725 P x f) = (term75 _89711 _89725 P x f).
Proof. exact (eq_refl (term75 _89711 _89725 P x f)). Qed.
Lemma lem3460098 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term135 _89711 _89725 t P x f) = (term136 _89711 _89725 t P x f).
Proof. exact (MK_COMB (@lem3460096 _89711 _89725 P f x t) (@lem3460097 _89711 _89725 P x f)). Qed.
Lemma lem3460099 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term137 _89711 _89725 P x f) = (term138 _89711 _89725 P x f).
Proof. exact (fun_ext (fun t : _89711 -> Prop => @lem3460098 _89711 _89725 t P x f)). Qed.
Lemma lem3460100 {_89711 : Type'} : (@ex (_89711 -> Prop)) = (@ex (_89711 -> Prop)).
Proof. exact (eq_refl (@ex (_89711 -> Prop))). Qed.
Lemma lem3460101 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term126 _89711 _89725 P x f) = (term139 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460100 _89711) (@lem3460099 _89711 _89725 P x f)). Qed.
Lemma lem3460102 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : ((term125 _89711 _89725 P x f) = (term126 _89711 _89725 P x f)) = ((term122 _89711 _89725 P x f) = (term139 _89711 _89725 P x f)).
Proof. exact (MK_COMB (@lem3460093 _89711 _89725 P x f) (@lem3460101 _89711 _89725 P x f)). Qed.
Lemma lem3460103 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term122 _89711 _89725 P x f) = (term139 _89711 _89725 P x f).
Proof. exact (EQ_MP (@lem3460102 _89711 _89725 P x f) (@lem3460083 _89711 _89725 P x f)). Qed.
Lemma lem3460105 {A : Type'} (P : A -> Prop) (Q : Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3460106 {_89725 : Type'} (P : _89725 -> Prop) (Q : Prop) : (term103 _89725 P Q) = (term104 _89725 P Q).
Proof. exact (@lem3460105 _89725 P Q). Qed.
Lemma lem3460107 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term140 _89711 _89725 t P x f) = (term141 _89711 _89725 t P x f).
Proof. exact (@lem3460106 _89725 (term117 _89711 _89725 P f x t) (term75 _89711 _89725 P x f)). Qed.
Lemma lem3460108 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89725) (x' : _89711) (t : _89711 -> Prop) : (term142 _89711 _89725 P f x' t x) = (term115 _89711 _89725 P f x x' t).
Proof. exact (eq_refl (term142 _89711 _89725 P f x' t x)). Qed.
Lemma lem3460109 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term143 _89711 _89725 P f x t) = (term117 _89711 _89725 P f x t).
Proof. exact (fun_ext (fun x' : _89725 => @lem3460108 _89711 _89725 P f x' x t)). Qed.
Lemma lem3460110 {_89725 : Type'} : (@ex _89725) = (@ex _89725).
Proof. exact (eq_refl (@ex _89725)). Qed.
Lemma lem3460111 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term144 _89711 _89725 P f x t) = (term118 _89711 _89725 P f x t).
Proof. exact (MK_COMB (@lem3460110 _89725) (@lem3460109 _89711 _89725 P f x t)). Qed.
Lemma lem3460112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3460113 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term145 _89711 _89725 P f x t) = (term134 _89711 _89725 P f x t).
Proof. exact (MK_COMB (@lem3460112) (@lem3460111 _89711 _89725 P f x t)). Qed.
Lemma lem3460114 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term75 _89711 _89725 P x f) = (term75 _89711 _89725 P x f).
Proof. exact (eq_refl (term75 _89711 _89725 P x f)). Qed.
Lemma lem3460115 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term140 _89711 _89725 t P x f) = (term136 _89711 _89725 t P x f).
Proof. exact (MK_COMB (@lem3460113 _89711 _89725 P f x t) (@lem3460114 _89711 _89725 P x f)). Qed.
Lemma lem3460116 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3460117 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term146 _89711 _89725 t P x f) = (term147 _89711 _89725 t P x f).
Proof. exact (MK_COMB (@lem3460116) (@lem3460115 _89711 _89725 t P x f)). Qed.
Lemma lem3460118 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89725) (x' : _89711) (t : _89711 -> Prop) : (term142 _89711 _89725 P f x' t x) = (term115 _89711 _89725 P f x x' t).
Proof. exact (eq_refl (term142 _89711 _89725 P f x' t x)). Qed.
Lemma lem3460119 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3460120 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89725) (x' : _89711) (t : _89711 -> Prop) : (term148 _89711 _89725 P f x' t x) = (term149 _89711 _89725 P f x x' t).
Proof. exact (MK_COMB (@lem3460119) (@lem3460118 _89711 _89725 P f x x' t)). Qed.
Lemma lem3460121 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term75 _89711 _89725 P x f) = (term75 _89711 _89725 P x f).
Proof. exact (eq_refl (term75 _89711 _89725 P x f)). Qed.
Lemma lem3460122 {_89711 _89725 : Type'} (x : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term150 _89711 _89725 t x P x' f) = (term151 _89711 _89725 x t P x' f).
Proof. exact (MK_COMB (@lem3460120 _89711 _89725 P f x x' t) (@lem3460121 _89711 _89725 P x' f)). Qed.
Lemma lem3460123 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term152 _89711 _89725 t P x f) = (term153 _89711 _89725 t P x f).
Proof. exact (fun_ext (fun x' : _89725 => @lem3460122 _89711 _89725 x' t P x f)). Qed.
Lemma lem3460124 {_89725 : Type'} : (@ex _89725) = (@ex _89725).
Proof. exact (eq_refl (@ex _89725)). Qed.
Lemma lem3460125 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term141 _89711 _89725 t P x f) = (term154 _89711 _89725 t P x f).
Proof. exact (MK_COMB (@lem3460124 _89725) (@lem3460123 _89711 _89725 t P x f)). Qed.
Lemma lem3460126 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : ((term140 _89711 _89725 t P x f) = (term141 _89711 _89725 t P x f)) = ((term136 _89711 _89725 t P x f) = (term154 _89711 _89725 t P x f)).
Proof. exact (MK_COMB (@lem3460117 _89711 _89725 t P x f) (@lem3460125 _89711 _89725 t P x f)). Qed.
Lemma lem3460127 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term136 _89711 _89725 t P x f) = (term154 _89711 _89725 t P x f).
Proof. exact (EQ_MP (@lem3460126 _89711 _89725 t P x f) (@lem3460107 _89711 _89725 t P x f)). Qed.
Lemma lem3460128 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term138 _89711 _89725 P x f) = (term155 _89711 _89725 P x f).
Proof. exact (fun_ext (fun t : _89711 -> Prop => @lem3460127 _89711 _89725 t P x f)). Qed.
Lemma lem3460129 {_89711 : Type'} : (@ex (_89711 -> Prop)) = (@ex (_89711 -> Prop)).
Proof. exact (eq_refl (@ex (_89711 -> Prop))). Qed.
Lemma lem3460130 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term139 _89711 _89725 P x f) = (term156 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460129 _89711) (@lem3460128 _89711 _89725 P x f)). Qed.
Lemma lem3460131 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term122 _89711 _89725 P x f) = (term156 _89711 _89725 P x f).
Proof. exact (TRANS (@lem3460103 _89711 _89725 P x f) (@lem3460130 _89711 _89725 P x f)). Qed.
Lemma lem3460132 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term79 _89711 _89725 P x f) = (term156 _89711 _89725 P x f).
Proof. exact (TRANS (@lem3460079 _89711 _89725 P x f) (@lem3460131 _89711 _89725 P x f)). Qed.
Lemma lem3460133 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term87 _89711 _89725 P x f) = (term157 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460048 _89711 _89725 P x f) (@lem3460132 _89711 _89725 P x f)). Qed.
Lemma lem3460137 {A : Type'} (P : A -> Prop) (Q : Prop) : (term158 A P Q) = (term159 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3460138 {_89725 : Type'} (P : _89725 -> Prop) (Q : Prop) : (term158 _89725 P Q) = (term159 _89725 P Q).
Proof. exact (@lem3460137 _89725 P Q). Qed.
Lemma lem3460139 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term160 _89711 _89725 P x f) = (term161 _89711 _89725 P x f).
Proof. exact (@lem3460138 _89725 (term100 _89711 _89725 P x f) (term156 _89711 _89725 P x f)). Qed.
Lemma lem3460140 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term162 _89711 _89725 P x f x') = (term98 _89711 _89725 P x f x').
Proof. exact (eq_refl (term162 _89711 _89725 P x f x')). Qed.
Lemma lem3460141 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term163 _89711 _89725 P x f) = (term100 _89711 _89725 P x f).
Proof. exact (fun_ext (fun x' : _89725 => @lem3460140 _89711 _89725 P x f x')). Qed.
Lemma lem3460142 {_89725 : Type'} : (@ex _89725) = (@ex _89725).
Proof. exact (eq_refl (@ex _89725)). Qed.
Lemma lem3460143 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term164 _89711 _89725 P x f) = (term101 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460142 _89725) (@lem3460141 _89711 _89725 P x f)). Qed.
Lemma lem3460144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3460145 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term165 _89711 _89725 P x f) = (term102 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460144) (@lem3460143 _89711 _89725 P x f)). Qed.
Lemma lem3460146 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term156 _89711 _89725 P x f) = (term156 _89711 _89725 P x f).
Proof. exact (eq_refl (term156 _89711 _89725 P x f)). Qed.
Lemma lem3460147 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term160 _89711 _89725 P x f) = (term157 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460145 _89711 _89725 P x f) (@lem3460146 _89711 _89725 P x f)). Qed.
Lemma lem3460148 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3460149 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term166 _89711 _89725 P x f) = (term167 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460148) (@lem3460147 _89711 _89725 P x f)). Qed.
Lemma lem3460150 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term162 _89711 _89725 P x f x') = (term98 _89711 _89725 P x f x').
Proof. exact (eq_refl (term162 _89711 _89725 P x f x')). Qed.
Lemma lem3460151 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3460152 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term168 _89711 _89725 P x f x') = (term169 _89711 _89725 P x f x').
Proof. exact (MK_COMB (@lem3460151) (@lem3460150 _89711 _89725 P x f x')). Qed.
Lemma lem3460153 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term156 _89711 _89725 P x f) = (term156 _89711 _89725 P x f).
Proof. exact (eq_refl (term156 _89711 _89725 P x f)). Qed.
Lemma lem3460154 {_89711 _89725 : Type'} (x : _89725) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term170 _89711 _89725 x P x' f) = (term171 _89711 _89725 x P x' f).
Proof. exact (MK_COMB (@lem3460152 _89711 _89725 P x' f x) (@lem3460153 _89711 _89725 P x' f)). Qed.
Lemma lem3460155 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term172 _89711 _89725 P x f) = (term173 _89711 _89725 P x f).
Proof. exact (fun_ext (fun x' : _89725 => @lem3460154 _89711 _89725 x' P x f)). Qed.
Lemma lem3460156 {_89725 : Type'} : (@ex _89725) = (@ex _89725).
Proof. exact (eq_refl (@ex _89725)). Qed.
Lemma lem3460157 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term161 _89711 _89725 P x f) = (term174 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460156 _89725) (@lem3460155 _89711 _89725 P x f)). Qed.
Lemma lem3460158 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : ((term160 _89711 _89725 P x f) = (term161 _89711 _89725 P x f)) = ((term157 _89711 _89725 P x f) = (term174 _89711 _89725 P x f)).
Proof. exact (MK_COMB (@lem3460149 _89711 _89725 P x f) (@lem3460157 _89711 _89725 P x f)). Qed.
Lemma lem3460159 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term157 _89711 _89725 P x f) = (term174 _89711 _89725 P x f).
Proof. exact (EQ_MP (@lem3460158 _89711 _89725 P x f) (@lem3460139 _89711 _89725 P x f)). Qed.
Lemma lem3460161 {A : Type'} (P : Prop) (Q : A -> Prop) : (term175 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3460162 {_89711 : Type'} (P : Prop) (Q : type686 _89711) : (term177 _89711 P Q) = (term178 _89711 P Q).
Proof. exact (@lem3460161 (_89711 -> Prop) P Q). Qed.
Lemma lem3460163 {_89711 _89725 : Type'} (x : _89725) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term179 _89711 _89725 x P x' f) = (term180 _89711 _89725 x P x' f).
Proof. exact (@lem3460162 _89711 (term98 _89711 _89725 P x' f x) (term155 _89711 _89725 P x' f)). Qed.
Lemma lem3460164 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term181 _89711 _89725 P x f t) = (term154 _89711 _89725 t P x f).
Proof. exact (eq_refl (term181 _89711 _89725 P x f t)). Qed.
Lemma lem3460165 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term182 _89711 _89725 P x f) = (term155 _89711 _89725 P x f).
Proof. exact (fun_ext (fun t : _89711 -> Prop => @lem3460164 _89711 _89725 t P x f)). Qed.
Lemma lem3460166 {_89711 : Type'} : (@ex (_89711 -> Prop)) = (@ex (_89711 -> Prop)).
Proof. exact (eq_refl (@ex (_89711 -> Prop))). Qed.
Lemma lem3460167 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term183 _89711 _89725 P x f) = (term156 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460166 _89711) (@lem3460165 _89711 _89725 P x f)). Qed.
Lemma lem3460168 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term169 _89711 _89725 P x f x') = (term169 _89711 _89725 P x f x').
Proof. exact (eq_refl (term169 _89711 _89725 P x f x')). Qed.
Lemma lem3460169 {_89711 _89725 : Type'} (x : _89725) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term179 _89711 _89725 x P x' f) = (term171 _89711 _89725 x P x' f).
Proof. exact (MK_COMB (@lem3460168 _89711 _89725 P x' f x) (@lem3460167 _89711 _89725 P x' f)). Qed.
Lemma lem3460170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3460171 {_89711 _89725 : Type'} (x : _89725) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term184 _89711 _89725 x P x' f) = (term185 _89711 _89725 x P x' f).
Proof. exact (MK_COMB (@lem3460170) (@lem3460169 _89711 _89725 x P x' f)). Qed.
Lemma lem3460172 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term181 _89711 _89725 P x f t) = (term154 _89711 _89725 t P x f).
Proof. exact (eq_refl (term181 _89711 _89725 P x f t)). Qed.
Lemma lem3460173 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term169 _89711 _89725 P x f x') = (term169 _89711 _89725 P x f x').
Proof. exact (eq_refl (term169 _89711 _89725 P x f x')). Qed.
Lemma lem3460174 {_89711 _89725 : Type'} (x : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term186 _89711 _89725 x P x' f t) = (term187 _89711 _89725 x t P x' f).
Proof. exact (MK_COMB (@lem3460173 _89711 _89725 P x' f x) (@lem3460172 _89711 _89725 t P x' f)). Qed.
Lemma lem3460175 {_89711 _89725 : Type'} (x : _89725) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term188 _89711 _89725 x P x' f) = (term189 _89711 _89725 x P x' f).
Proof. exact (fun_ext (fun t : _89711 -> Prop => @lem3460174 _89711 _89725 x t P x' f)). Qed.
Lemma lem3460176 {_89711 : Type'} : (@ex (_89711 -> Prop)) = (@ex (_89711 -> Prop)).
Proof. exact (eq_refl (@ex (_89711 -> Prop))). Qed.
Lemma lem3460177 {_89711 _89725 : Type'} (x : _89725) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term180 _89711 _89725 x P x' f) = (term190 _89711 _89725 x P x' f).
Proof. exact (MK_COMB (@lem3460176 _89711) (@lem3460175 _89711 _89725 x P x' f)). Qed.
Lemma lem3460178 {_89711 _89725 : Type'} (x : _89725) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : ((term179 _89711 _89725 x P x' f) = (term180 _89711 _89725 x P x' f)) = ((term171 _89711 _89725 x P x' f) = (term190 _89711 _89725 x P x' f)).
Proof. exact (MK_COMB (@lem3460171 _89711 _89725 x P x' f) (@lem3460177 _89711 _89725 x P x' f)). Qed.
Lemma lem3460179 {_89711 _89725 : Type'} (x : _89725) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term171 _89711 _89725 x P x' f) = (term190 _89711 _89725 x P x' f).
Proof. exact (EQ_MP (@lem3460178 _89711 _89725 x P x' f) (@lem3460163 _89711 _89725 x P x' f)). Qed.
Lemma lem3460181 {A : Type'} (P : Prop) (Q : A -> Prop) : (term175 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3460182 {_89725 : Type'} (P : Prop) (Q : _89725 -> Prop) : (term175 _89725 P Q) = (term176 _89725 P Q).
Proof. exact (@lem3460181 _89725 P Q). Qed.
Lemma lem3460183 {_89711 _89725 : Type'} (x : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term191 _89711 _89725 x t P x' f) = (term192 _89711 _89725 x t P x' f).
Proof. exact (@lem3460182 _89725 (term98 _89711 _89725 P x' f x) (term153 _89711 _89725 t P x' f)). Qed.
Lemma lem3460184 {_89711 _89725 : Type'} (x : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term193 _89711 _89725 t P x' f x) = (term151 _89711 _89725 x t P x' f).
Proof. exact (eq_refl (term193 _89711 _89725 t P x' f x)). Qed.
Lemma lem3460185 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term194 _89711 _89725 t P x f) = (term153 _89711 _89725 t P x f).
Proof. exact (fun_ext (fun x' : _89725 => @lem3460184 _89711 _89725 x' t P x f)). Qed.
Lemma lem3460186 {_89725 : Type'} : (@ex _89725) = (@ex _89725).
Proof. exact (eq_refl (@ex _89725)). Qed.
Lemma lem3460187 {_89711 _89725 : Type'} (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term195 _89711 _89725 t P x f) = (term154 _89711 _89725 t P x f).
Proof. exact (MK_COMB (@lem3460186 _89725) (@lem3460185 _89711 _89725 t P x f)). Qed.
Lemma lem3460188 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term169 _89711 _89725 P x f x') = (term169 _89711 _89725 P x f x').
Proof. exact (eq_refl (term169 _89711 _89725 P x f x')). Qed.
Lemma lem3460189 {_89711 _89725 : Type'} (x : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term191 _89711 _89725 x t P x' f) = (term187 _89711 _89725 x t P x' f).
Proof. exact (MK_COMB (@lem3460188 _89711 _89725 P x' f x) (@lem3460187 _89711 _89725 t P x' f)). Qed.
Lemma lem3460190 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3460191 {_89711 _89725 : Type'} (x : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term196 _89711 _89725 x t P x' f) = (term197 _89711 _89725 x t P x' f).
Proof. exact (MK_COMB (@lem3460190) (@lem3460189 _89711 _89725 x t P x' f)). Qed.
Lemma lem3460192 {_89711 _89725 : Type'} (x' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term193 _89711 _89725 t P x f x') = (term151 _89711 _89725 x' t P x f).
Proof. exact (eq_refl (term193 _89711 _89725 t P x f x')). Qed.
Lemma lem3460193 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term169 _89711 _89725 P x f x') = (term169 _89711 _89725 P x f x').
Proof. exact (eq_refl (term169 _89711 _89725 P x f x')). Qed.
Lemma lem3460194 {_89711 _89725 : Type'} (x : _89725) (x' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x'' : _89711) (f : type1470 _89711 _89725) : (term198 _89711 _89725 x t P x'' f x') = (term199 _89711 _89725 x x' t P x'' f).
Proof. exact (MK_COMB (@lem3460193 _89711 _89725 P x'' f x) (@lem3460192 _89711 _89725 x' t P x'' f)). Qed.
Lemma lem3460195 {_89711 _89725 : Type'} (x : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term200 _89711 _89725 x t P x' f) = (term201 _89711 _89725 x t P x' f).
Proof. exact (fun_ext (fun x'' : _89725 => @lem3460194 _89711 _89725 x x'' t P x' f)). Qed.
Lemma lem3460196 {_89725 : Type'} : (@ex _89725) = (@ex _89725).
Proof. exact (eq_refl (@ex _89725)). Qed.
Lemma lem3460197 {_89711 _89725 : Type'} (x : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term192 _89711 _89725 x t P x' f) = (term202 _89711 _89725 x t P x' f).
Proof. exact (MK_COMB (@lem3460196 _89725) (@lem3460195 _89711 _89725 x t P x' f)). Qed.
Lemma lem3460198 {_89711 _89725 : Type'} (x : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : ((term191 _89711 _89725 x t P x' f) = (term192 _89711 _89725 x t P x' f)) = ((term187 _89711 _89725 x t P x' f) = (term202 _89711 _89725 x t P x' f)).
Proof. exact (MK_COMB (@lem3460191 _89711 _89725 x t P x' f) (@lem3460197 _89711 _89725 x t P x' f)). Qed.
Lemma lem3460199 {_89711 _89725 : Type'} (x : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term187 _89711 _89725 x t P x' f) = (term202 _89711 _89725 x t P x' f).
Proof. exact (EQ_MP (@lem3460198 _89711 _89725 x t P x' f) (@lem3460183 _89711 _89725 x t P x' f)). Qed.
Lemma lem3460200 {_89711 _89725 : Type'} (x : _89725) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term189 _89711 _89725 x P x' f) = (term203 _89711 _89725 x P x' f).
Proof. exact (fun_ext (fun t : _89711 -> Prop => @lem3460199 _89711 _89725 x t P x' f)). Qed.
Lemma lem3460201 {_89711 : Type'} : (@ex (_89711 -> Prop)) = (@ex (_89711 -> Prop)).
Proof. exact (eq_refl (@ex (_89711 -> Prop))). Qed.
Lemma lem3460202 {_89711 _89725 : Type'} (x : _89725) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term190 _89711 _89725 x P x' f) = (term204 _89711 _89725 x P x' f).
Proof. exact (MK_COMB (@lem3460201 _89711) (@lem3460200 _89711 _89725 x P x' f)). Qed.
Lemma lem3460203 {_89711 _89725 : Type'} (x : _89725) (P : _89725 -> Prop) (x' : _89711) (f : type1470 _89711 _89725) : (term171 _89711 _89725 x P x' f) = (term204 _89711 _89725 x P x' f).
Proof. exact (TRANS (@lem3460179 _89711 _89725 x P x' f) (@lem3460202 _89711 _89725 x P x' f)). Qed.
Lemma lem3460204 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term173 _89711 _89725 P x f) = (term205 _89711 _89725 P x f).
Proof. exact (fun_ext (fun x' : _89725 => @lem3460203 _89711 _89725 x' P x f)). Qed.
Lemma lem3460205 {_89725 : Type'} : (@ex _89725) = (@ex _89725).
Proof. exact (eq_refl (@ex _89725)). Qed.
Lemma lem3460206 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term174 _89711 _89725 P x f) = (term206 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460205 _89725) (@lem3460204 _89711 _89725 P x f)). Qed.
Lemma lem3460207 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term157 _89711 _89725 P x f) = (term206 _89711 _89725 P x f).
Proof. exact (TRANS (@lem3460159 _89711 _89725 P x f) (@lem3460206 _89711 _89725 P x f)). Qed.
Lemma lem3460209 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term87 _89711 _89725 P x f) = (term206 _89711 _89725 P x f).
Proof. exact (TRANS (@lem3460133 _89711 _89725 P x f) (@lem3460207 _89711 _89725 P x f)). Qed.
Lemma lem3460210 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term30 _89711 _89725 P x f) = (term206 _89711 _89725 P x f).
Proof. exact (TRANS (@lem3459777 _89711 _89725 P x f) (@lem3460209 _89711 _89725 P x f)). Qed.
Lemma lem3460211 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term30 _89711 _89725 P x f) : term206 _89711 _89725 P x f.
Proof. exact (EQ_MP (@lem3460210 _89711 _89725 P x f) (@lem3459689 _89711 _89725 P x f h1)). Qed.
Lemma lem3460212 {_89711 _89725 : Type'} (x' : _89725) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term204 _89711 _89725 x' P x f) : term204 _89711 _89725 x' P x f.
Proof. exact (h1). Qed.
Lemma lem3460213 {_89711 _89725 : Type'} (x' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term202 _89711 _89725 x' t P x f) : term202 _89711 _89725 x' t P x f.
Proof. exact (h1). Qed.
Lemma lem3460214 {_89711 _89725 : Type'} (x' : _89725) (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term199 _89711 _89725 x' x'' t P x f) : term199 _89711 _89725 x' x'' t P x f.
Proof. exact (h1). Qed.
Lemma lem3460229 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term64 _89711 _89725 P x f x') = (term64 _89711 _89725 P x f x').
Proof. exact (eq_refl (term64 _89711 _89725 P x f x')). Qed.
Lemma lem3460230 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term74 _89711 _89725 P x f) = (term74 _89711 _89725 P x f).
Proof. exact (fun_ext (fun x' : _89725 => @lem3460229 _89711 _89725 P x f x')). Qed.
Lemma lem3460231 {_89725 : Type'} : (@all _89725) = (@all _89725).
Proof. exact (eq_refl (@all _89725)). Qed.
Lemma lem3460232 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term75 _89711 _89725 P x f) = (term75 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460231 _89725) (@lem3460230 _89711 _89725 P x f)). Qed.
Lemma lem3460257 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x'' : _89725) (x : _89711) (t : _89711 -> Prop) : (term149 _89711 _89725 P f x'' x t) = (term149 _89711 _89725 P f x'' x t).
Proof. exact (eq_refl (term149 _89711 _89725 P f x'' x t)). Qed.
Lemma lem3460258 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term151 _89711 _89725 x'' t P x f) = (term151 _89711 _89725 x'' t P x f).
Proof. exact (MK_COMB (@lem3460257 _89711 _89725 P f x'' x t) (@lem3460232 _89711 _89725 P x f)). Qed.
Lemma lem3460273 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term62 _89711 _89725 P x f x') = (term62 _89711 _89725 P x f x').
Proof. exact (eq_refl (term62 _89711 _89725 P x f x')). Qed.
Lemma lem3460278 {_89711 : Type'} (x : _89711) (t : _89711 -> Prop) : (@IN _89711 x t) = (@IN _89711 x t).
Proof. exact (eq_refl (@IN _89711 x t)). Qed.
Lemma lem3460295 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term32 _89711 _89725 P t f x) = (term32 _89711 _89725 P t f x).
Proof. exact (eq_refl (term32 _89711 _89725 P t f x)). Qed.
Lemma lem3460296 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term40 _89711 _89725 P t f) = (term40 _89711 _89725 P t f).
Proof. exact (fun_ext (fun x : _89725 => @lem3460295 _89711 _89725 P t f x)). Qed.
Lemma lem3460297 {_89725 : Type'} : (@all _89725) = (@all _89725).
Proof. exact (eq_refl (@all _89725)). Qed.
Lemma lem3460298 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term41 _89711 _89725 P t f) = (term41 _89711 _89725 P t f).
Proof. exact (MK_COMB (@lem3460297 _89725) (@lem3460296 _89711 _89725 P t f)). Qed.
Lemma lem3460299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3460300 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term47 _89711 _89725 P t f) = (term47 _89711 _89725 P t f).
Proof. exact (MK_COMB (@lem3460299) (@lem3460298 _89711 _89725 P t f)). Qed.
Lemma lem3460301 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term49 _89711 _89725 P f x t) = (term49 _89711 _89725 P f x t).
Proof. exact (MK_COMB (@lem3460300 _89711 _89725 P t f) (@lem3460278 _89711 x t)). Qed.
Lemma lem3460302 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term59 _89711 _89725 P f x) = (term59 _89711 _89725 P f x).
Proof. exact (fun_ext (fun t : _89711 -> Prop => @lem3460301 _89711 _89725 P f x t)). Qed.
Lemma lem3460303 {_89711 : Type'} : (@all (_89711 -> Prop)) = (@all (_89711 -> Prop)).
Proof. exact (eq_refl (@all (_89711 -> Prop))). Qed.
Lemma lem3460304 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term60 _89711 _89725 P f x) = (term60 _89711 _89725 P f x).
Proof. exact (MK_COMB (@lem3460303 _89711) (@lem3460302 _89711 _89725 P f x)). Qed.
Lemma lem3460305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3460306 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term81 _89711 _89725 P f x) = (term81 _89711 _89725 P f x).
Proof. exact (MK_COMB (@lem3460305) (@lem3460304 _89711 _89725 P f x)). Qed.
Lemma lem3460307 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term98 _89711 _89725 P x f x') = (term98 _89711 _89725 P x f x').
Proof. exact (MK_COMB (@lem3460306 _89711 _89725 P f x) (@lem3460273 _89711 _89725 P x f x')). Qed.
Lemma lem3460308 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3460309 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term169 _89711 _89725 P x f x') = (term169 _89711 _89725 P x f x').
Proof. exact (MK_COMB (@lem3460308) (@lem3460307 _89711 _89725 P x f x')). Qed.
Lemma lem3460310 {_89711 _89725 : Type'} (x' : _89725) (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term199 _89711 _89725 x' x'' t P x f) = (term199 _89711 _89725 x' x'' t P x f).
Proof. exact (MK_COMB (@lem3460309 _89711 _89725 P x f x') (@lem3460258 _89711 _89725 x'' t P x f)). Qed.
Lemma lem3460311 {_89711 _89725 : Type'} (x' : _89725) (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term199 _89711 _89725 x' x'' t P x f) : term199 _89711 _89725 x' x'' t P x f.
Proof. exact (EQ_MP (@lem3460310 _89711 _89725 x' x'' t P x f) (@lem3460214 _89711 _89725 x' x'' t P x f h1)). Qed.
Lemma lem3460312 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term98 _89711 _89725 P x f x'.
Proof. exact (h1). Qed.
Lemma lem3460313 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term151 _89711 _89725 x'' t P x f.
Proof. exact (h1). Qed.
Lemma lem3460314 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term62 _89711 _89725 P x f x'.
Proof. exact (proj2 (@lem3460312 _89711 _89725 P x f x' h1)). Qed.
Lemma lem3460315 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term60 _89711 _89725 P f x.
Proof. exact (proj1 (@lem3460312 _89711 _89725 P x f x' h1)). Qed.
Lemma lem3460318 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term75 _89711 _89725 P x f.
Proof. exact (proj2 (@lem3460313 _89711 _89725 x'' t P x f h1)). Qed.
Lemma lem3460319 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term115 _89711 _89725 P f x'' x t.
Proof. exact (proj1 (@lem3460313 _89711 _89725 x'' t P x f h1)). Qed.
Lemma lem3460321 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term20 _89711 _89725 P t f x''.
Proof. exact (proj1 (@lem3460319 _89711 _89725 x'' t P x f h1)). Qed.
Lemma lem3460325 {A : Type'} (P : A -> Prop) (Q : Prop) : (term207 A P Q) = (term208 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3460326 {_89725 : Type'} (P : _89725 -> Prop) (Q : Prop) : (term207 _89725 P Q) = (term208 _89725 P Q).
Proof. exact (@lem3460325 _89725 P Q). Qed.
Lemma lem3460327 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term209 _89711 _89725 P f x t) = (term210 _89711 _89725 P f x t).
Proof. exact (@lem3460326 _89725 (term40 _89711 _89725 P t f) (@IN _89711 x t)). Qed.
Lemma lem3460328 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term211 _89711 _89725 P t f x) = (term32 _89711 _89725 P t f x).
Proof. exact (eq_refl (term211 _89711 _89725 P t f x)). Qed.
Lemma lem3460329 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term212 _89711 _89725 P t f) = (term40 _89711 _89725 P t f).
Proof. exact (fun_ext (fun x : _89725 => @lem3460328 _89711 _89725 P t f x)). Qed.
Lemma lem3460330 {_89725 : Type'} : (@all _89725) = (@all _89725).
Proof. exact (eq_refl (@all _89725)). Qed.
Lemma lem3460331 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term213 _89711 _89725 P t f) = (term41 _89711 _89725 P t f).
Proof. exact (MK_COMB (@lem3460330 _89725) (@lem3460329 _89711 _89725 P t f)). Qed.
Lemma lem3460332 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3460333 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) : (term214 _89711 _89725 P t f) = (term47 _89711 _89725 P t f).
Proof. exact (MK_COMB (@lem3460332) (@lem3460331 _89711 _89725 P t f)). Qed.
Lemma lem3460334 {_89711 : Type'} (x : _89711) (t : _89711 -> Prop) : (@IN _89711 x t) = (@IN _89711 x t).
Proof. exact (eq_refl (@IN _89711 x t)). Qed.
Lemma lem3460335 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term209 _89711 _89725 P f x t) = (term49 _89711 _89725 P f x t).
Proof. exact (MK_COMB (@lem3460333 _89711 _89725 P t f) (@lem3460334 _89711 x t)). Qed.
Lemma lem3460336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3460337 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term215 _89711 _89725 P f x t) = (term216 _89711 _89725 P f x t).
Proof. exact (MK_COMB (@lem3460336) (@lem3460335 _89711 _89725 P f x t)). Qed.
Lemma lem3460338 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term211 _89711 _89725 P t f x) = (term32 _89711 _89725 P t f x).
Proof. exact (eq_refl (term211 _89711 _89725 P t f x)). Qed.
Lemma lem3460339 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3460340 {_89711 _89725 : Type'} (P : _89725 -> Prop) (t : _89711 -> Prop) (f : type1470 _89711 _89725) (x : _89725) : (term217 _89711 _89725 P t f x) = (term218 _89711 _89725 P t f x).
Proof. exact (MK_COMB (@lem3460339) (@lem3460338 _89711 _89725 P t f x)). Qed.
Lemma lem3460341 {_89711 : Type'} (x : _89711) (t : _89711 -> Prop) : (@IN _89711 x t) = (@IN _89711 x t).
Proof. exact (eq_refl (@IN _89711 x t)). Qed.
Lemma lem3460342 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89725) (x' : _89711) (t : _89711 -> Prop) : (term219 _89711 _89725 P f x x' t) = (term220 _89711 _89725 P f x x' t).
Proof. exact (MK_COMB (@lem3460340 _89711 _89725 P t f x) (@lem3460341 _89711 x' t)). Qed.
Lemma lem3460343 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term221 _89711 _89725 P f x t) = (term222 _89711 _89725 P f x t).
Proof. exact (fun_ext (fun x' : _89725 => @lem3460342 _89711 _89725 P f x' x t)). Qed.
Lemma lem3460344 {_89725 : Type'} : (@all _89725) = (@all _89725).
Proof. exact (eq_refl (@all _89725)). Qed.
Lemma lem3460345 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term210 _89711 _89725 P f x t) = (term223 _89711 _89725 P f x t).
Proof. exact (MK_COMB (@lem3460344 _89725) (@lem3460343 _89711 _89725 P f x t)). Qed.
Lemma lem3460346 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : ((term209 _89711 _89725 P f x t) = (term210 _89711 _89725 P f x t)) = ((term49 _89711 _89725 P f x t) = (term223 _89711 _89725 P f x t)).
Proof. exact (MK_COMB (@lem3460337 _89711 _89725 P f x t) (@lem3460345 _89711 _89725 P f x t)). Qed.
Lemma lem3460347 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term49 _89711 _89725 P f x t) = (term223 _89711 _89725 P f x t).
Proof. exact (EQ_MP (@lem3460346 _89711 _89725 P f x t) (@lem3460327 _89711 _89725 P f x t)). Qed.
Lemma lem3460348 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term59 _89711 _89725 P f x) = (term224 _89711 _89725 P f x).
Proof. exact (fun_ext (fun t : _89711 -> Prop => @lem3460347 _89711 _89725 P f x t)). Qed.
Lemma lem3460349 {_89711 : Type'} : (@all (_89711 -> Prop)) = (@all (_89711 -> Prop)).
Proof. exact (eq_refl (@all (_89711 -> Prop))). Qed.
Lemma lem3460350 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term60 _89711 _89725 P f x) = (term225 _89711 _89725 P f x).
Proof. exact (MK_COMB (@lem3460349 _89711) (@lem3460348 _89711 _89725 P f x)). Qed.
Lemma lem3460363 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89725) (x' : _89711) (t : _89711 -> Prop) : (term220 _89711 _89725 P f x x' t) = (term220 _89711 _89725 P f x x' t).
Proof. exact (eq_refl (term220 _89711 _89725 P f x x' t)). Qed.
Lemma lem3460364 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term222 _89711 _89725 P f x t) = (term222 _89711 _89725 P f x t).
Proof. exact (fun_ext (fun x' : _89725 => @lem3460363 _89711 _89725 P f x' x t)). Qed.
Lemma lem3460365 {_89725 : Type'} : (@all _89725) = (@all _89725).
Proof. exact (eq_refl (@all _89725)). Qed.
Lemma lem3460366 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (t : _89711 -> Prop) : (term223 _89711 _89725 P f x t) = (term223 _89711 _89725 P f x t).
Proof. exact (MK_COMB (@lem3460365 _89725) (@lem3460364 _89711 _89725 P f x t)). Qed.
Lemma lem3460367 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term224 _89711 _89725 P f x) = (term224 _89711 _89725 P f x).
Proof. exact (fun_ext (fun t : _89711 -> Prop => @lem3460366 _89711 _89725 P f x t)). Qed.
Lemma lem3460368 {_89711 : Type'} : (@all (_89711 -> Prop)) = (@all (_89711 -> Prop)).
Proof. exact (eq_refl (@all (_89711 -> Prop))). Qed.
Lemma lem3460369 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term225 _89711 _89725 P f x) = (term225 _89711 _89725 P f x).
Proof. exact (MK_COMB (@lem3460368 _89711) (@lem3460367 _89711 _89725 P f x)). Qed.
Lemma lem3460370 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) : (term60 _89711 _89725 P f x) = (term225 _89711 _89725 P f x).
Proof. exact (TRANS (@lem3460350 _89711 _89725 P f x) (@lem3460369 _89711 _89725 P f x)). Qed.
Lemma lem3460371 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term225 _89711 _89725 P f x.
Proof. exact (EQ_MP (@lem3460370 _89711 _89725 P f x) (@lem3460315 _89711 _89725 P x f x' h1)). Qed.
Lemma lem3460387 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term64 _89711 _89725 P x f x') = (term64 _89711 _89725 P x f x').
Proof. exact (eq_refl (term64 _89711 _89725 P x f x')). Qed.
Lemma lem3460388 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term74 _89711 _89725 P x f) = (term74 _89711 _89725 P x f).
Proof. exact (fun_ext (fun x' : _89725 => @lem3460387 _89711 _89725 P x f x')). Qed.
Lemma lem3460389 {_89725 : Type'} : (@all _89725) = (@all _89725).
Proof. exact (eq_refl (@all _89725)). Qed.
Lemma lem3460391 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term75 _89711 _89725 P x f) = (term75 _89711 _89725 P x f).
Proof. exact (MK_COMB (@lem3460389 _89725) (@lem3460388 _89711 _89725 P x f)). Qed.
Lemma lem3460392 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term75 _89711 _89725 P x f.
Proof. exact (EQ_MP (@lem3460391 _89711 _89725 P x f) (@lem3460318 _89711 _89725 x'' t P x f h1)). Qed.
Lemma lem3460405 {_89711 _89725 : Type'} (_36520 : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term226 _89711 _89725 P f x _36520.
Proof. exact (@lem3460371 _89711 _89725 P x f x' h1 _36520). Qed.
Lemma lem3460406 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (x : _89711) (_36520 : _89711 -> Prop) : (term226 _89711 _89725 P f x _36520) = (term223 _89711 _89725 P f x _36520).
Proof. exact (eq_refl (term226 _89711 _89725 P f x _36520)). Qed.
Lemma lem3460407 {_89711 _89725 : Type'} (_36520 : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term223 _89711 _89725 P f x _36520.
Proof. exact (EQ_MP (@lem3460406 _89711 _89725 P f x _36520) (@lem3460405 _89711 _89725 _36520 P x f x' h1)). Qed.
Lemma lem3460408 {_89711 _89725 : Type'} (_36520 : _89711 -> Prop) (_36521 : _89725) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term227 _89711 _89725 P f x _36520 _36521.
Proof. exact (@lem3460407 _89711 _89725 _36520 P x f x' h1 _36521). Qed.
Lemma lem3460409 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) (x : _89711) (_36520 : _89711 -> Prop) : (term227 _89711 _89725 P f x _36520 _36521) = (term220 _89711 _89725 P f _36521 x _36520).
Proof. exact (eq_refl (term227 _89711 _89725 P f x _36520 _36521)). Qed.
Lemma lem3460410 {_89711 _89725 : Type'} (_36521 : _89725) (_36520 : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term220 _89711 _89725 P f _36521 x _36520.
Proof. exact (EQ_MP (@lem3460409 _89711 _89725 P f _36521 x _36520) (@lem3460408 _89711 _89725 _36520 _36521 P x f x' h1)). Qed.
Lemma lem3460411 {_89711 _89725 : Type'} (_36522 : _89725) (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term228 _89711 _89725 P x f _36522.
Proof. exact (@lem3460392 _89711 _89725 x'' t P x f h1 _36522). Qed.
Lemma lem3460412 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (_36522 : _89725) : (term228 _89711 _89725 P x f _36522) = (term64 _89711 _89725 P x f _36522).
Proof. exact (eq_refl (term228 _89711 _89725 P x f _36522)). Qed.
Lemma lem3460424 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) (x : _89711) (_36520 : _89711 -> Prop) : (term220 _89711 _89725 P f _36521 x _36520) = (term229 _89711 _89725 P f _36521 x _36520).
Proof. exact (@lem3458986 (term230 _89725 P _36521) (term231 _89711 _89725 _36520 f _36521) (@IN _89711 x _36520)). Qed.
Lemma lem3460425 {_89711 _89725 : Type'} (_36521 : _89725) (_36520 : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term229 _89711 _89725 P f _36521 x _36520.
Proof. exact (EQ_MP (@lem3460424 _89711 _89725 P f _36521 x _36520) (@lem3460410 _89711 _89725 _36521 _36520 P x f x' h1)). Qed.
Lemma lem3460429 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term232 _89711 _89725 x f x'.
Proof. exact (proj2 (@lem3460314 _89711 _89725 P x f x' h1)). Qed.
Lemma lem3460437 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term42 _89711 x t.
Proof. exact (proj2 (@lem3460319 _89711 _89725 x'' t P x f h1)). Qed.
Lemma lem3460441 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : t = (f x'').
Proof. exact (proj2 (@lem3460321 _89711 _89725 x'' t P x f h1)). Qed.
Lemma lem3460469 {_89711 _89725 : Type'} (_36522 : _89725) (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term64 _89711 _89725 P x f _36522.
Proof. exact (EQ_MP (@lem3460412 _89711 _89725 P x f _36522) (@lem3460411 _89711 _89725 _36522 x'' t P x f h1)). Qed.
Lemma lem3460470 {_89711 : Type'} (x : _89711) : (term233 _89711 x) = (term233 _89711 x).
Proof. exact (eq_refl (term233 _89711 x)). Qed.
Lemma lem3460471 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : (term234 _89711 x t) = (term235 _89711 _89725 x f x'').
Proof. exact (MK_COMB (@lem3460470 _89711 x) (@lem3460441 _89711 _89725 x'' t P x f h1)). Qed.
Lemma lem3460472 {_89711 _89725 : Type'} (x : _89711) (f : type1470 _89711 _89725) (x'' : _89725) : (term235 _89711 _89725 x f x'') = (term232 _89711 _89725 x f x'').
Proof. exact (eq_refl (term235 _89711 _89725 x f x'')). Qed.
Lemma lem3460473 {_89711 : Type'} (x : _89711) (t : _89711 -> Prop) : (term236 _89711 x t) = (term236 _89711 x t).
Proof. exact (eq_refl (term236 _89711 x t)). Qed.
Lemma lem3460474 {_89711 _89725 : Type'} (t : _89711 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x'' : _89725) : ((term234 _89711 x t) = (term235 _89711 _89725 x f x'')) = ((term234 _89711 x t) = (term232 _89711 _89725 x f x'')).
Proof. exact (MK_COMB (@lem3460473 _89711 x t) (@lem3460472 _89711 _89725 x f x'')). Qed.
Lemma lem3460475 {_89711 : Type'} (x : _89711) (t : _89711 -> Prop) : (term234 _89711 x t) = (term42 _89711 x t).
Proof. exact (eq_refl (term234 _89711 x t)). Qed.
Lemma lem3460476 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3460477 {_89711 : Type'} (x : _89711) (t : _89711 -> Prop) : (term236 _89711 x t) = (term237 _89711 x t).
Proof. exact (MK_COMB (@lem3460476) (@lem3460475 _89711 x t)). Qed.
Lemma lem3460478 {_89711 _89725 : Type'} (x : _89711) (f : type1470 _89711 _89725) (x'' : _89725) : (term232 _89711 _89725 x f x'') = (term232 _89711 _89725 x f x'').
Proof. exact (eq_refl (term232 _89711 _89725 x f x'')). Qed.
Lemma lem3460479 {_89711 _89725 : Type'} (t : _89711 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x'' : _89725) : ((term234 _89711 x t) = (term232 _89711 _89725 x f x'')) = ((term42 _89711 x t) = (term232 _89711 _89725 x f x'')).
Proof. exact (MK_COMB (@lem3460477 _89711 x t) (@lem3460478 _89711 _89725 x f x'')). Qed.
Lemma lem3460480 {_89711 _89725 : Type'} (t : _89711 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x'' : _89725) : ((term234 _89711 x t) = (term235 _89711 _89725 x f x'')) = ((term42 _89711 x t) = (term232 _89711 _89725 x f x'')).
Proof. exact (TRANS (@lem3460474 _89711 _89725 t x f x'') (@lem3460479 _89711 _89725 t x f x'')). Qed.
Lemma lem3460481 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : (term42 _89711 x t) = (term232 _89711 _89725 x f x'').
Proof. exact (EQ_MP (@lem3460480 _89711 _89725 t x f x'') (@lem3460471 _89711 _89725 x'' t P x f h1)). Qed.
Lemma lem3460482 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term232 _89711 _89725 x f x''.
Proof. exact (EQ_MP (@lem3460481 _89711 _89725 x'' t P x f h1) (@lem3460437 _89711 _89725 x'' t P x f h1)). Qed.
Lemma lem3460543 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : P x'.
Proof. exact (proj1 (@lem3460314 _89711 _89725 P x f x' h1)). Qed.
Lemma lem3460544 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term238 _89725 P x'.
Proof. exact (fun h0 : term230 _89725 P x' => @lem3460543 _89711 _89725 P x f x' h1). Qed.
Lemma lem3460546 (p : Prop) : (term239 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3460547 {_89725 : Type'} (P : _89725 -> Prop) (x' : _89725) : (term238 _89725 P x') = (P x').
Proof. exact (@lem3460546 (P x')). Qed.
Lemma lem3460548 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : P x'.
Proof. exact (EQ_MP (@lem3460547 _89725 P x') (@lem3460544 _89711 _89725 P x f x' h1)). Qed.
Lemma lem3460550 {_89711 : Type'} (x : _89711 -> Prop) : x = x.
Proof. exact (@lem21386 (_89711 -> Prop) x). Qed.
Lemma lem3460551 {_89711 : Type'} (x : _89711 -> Prop) : x = x.
Proof. exact (@lem3460550 _89711 x). Qed.
Lemma lem3460552 {_89711 _89725 : Type'} (f : type1470 _89711 _89725) (x' : _89725) : (f x') = (f x').
Proof. exact (@lem3460551 _89711 (f x')). Qed.
Lemma lem3460553 {_89711 _89725 : Type'} (f : type1470 _89711 _89725) (x' : _89725) : term240 _89711 _89725 f x'.
Proof. exact (fun h0 : term241 _89711 _89725 f x' => @lem3460552 _89711 _89725 f x'). Qed.
Lemma lem3460555 (p : Prop) : (term239 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3460556 {_89711 _89725 : Type'} (f : type1470 _89711 _89725) (x' : _89725) : (term240 _89711 _89725 f x') = ((f x') = (f x')).
Proof. exact (@lem3460555 ((f x') = (f x'))). Qed.
Lemma lem3460557 {_89711 _89725 : Type'} (f : type1470 _89711 _89725) (x' : _89725) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3460556 _89711 _89725 f x') (@lem3460553 _89711 _89725 f x')). Qed.
Lemma lem3460573 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3460574 {_89711 _89725 : Type'} (x : _89711) (_36520 : _89711 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) : (term242 _89711 _89725 f _36521 x _36520) = (term243 _89711 _89725 x _36520 f _36521).
Proof. exact (@lem3460573 (@IN _89711 x _36520) (term231 _89711 _89725 _36520 f _36521)). Qed.
Lemma lem3460582 {_89725 : Type'} (P : _89725 -> Prop) (_36521 : _89725) : (term244 _89725 P _36521) = (term244 _89725 P _36521).
Proof. exact (eq_refl (term244 _89725 P _36521)). Qed.
Lemma lem3460583 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (_36520 : _89711 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) : (term229 _89711 _89725 P f _36521 x _36520) = (term245 _89711 _89725 P x _36520 f _36521).
Proof. exact (MK_COMB (@lem3460582 _89725 P _36521) (@lem3460574 _89711 _89725 x _36520 f _36521)). Qed.
Lemma lem3460587 (q : Prop) (p : Prop) (r : Prop) : (term246 p q r) = (term246 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3460588 {_89711 _89725 : Type'} (x : _89711) (P : _89725 -> Prop) (_36520 : _89711 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) : (term245 _89711 _89725 P x _36520 f _36521) = (term247 _89711 _89725 x P _36520 f _36521).
Proof. exact (@lem3460587 (@IN _89711 x _36520) (term230 _89725 P _36521) (term231 _89711 _89725 _36520 f _36521)). Qed.
Lemma lem3460606 {_89711 _89725 : Type'} (x : _89711) (P : _89725 -> Prop) (_36520 : _89711 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) : (term229 _89711 _89725 P f _36521 x _36520) = (term247 _89711 _89725 x P _36520 f _36521).
Proof. exact (TRANS (@lem3460583 _89711 _89725 P x _36520 f _36521) (@lem3460588 _89711 _89725 x P _36520 f _36521)). Qed.
Lemma lem3460607 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3460608 {_89711 _89725 : Type'} (x : _89711) (P : _89725 -> Prop) (_36520 : _89711 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) : (term248 _89711 _89725 P f _36521 x _36520) = (term249 _89711 _89725 x P _36520 f _36521).
Proof. exact (MK_COMB (@lem3460607) (@lem3460606 _89711 _89725 x P _36520 f _36521)). Qed.
Lemma lem3460626 {_89711 _89725 : Type'} (x : _89711) (P : _89725 -> Prop) (_36520 : _89711 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) : (term247 _89711 _89725 x P _36520 f _36521) = (term247 _89711 _89725 x P _36520 f _36521).
Proof. exact (eq_refl (term247 _89711 _89725 x P _36520 f _36521)). Qed.
Lemma lem3460627 {_89711 _89725 : Type'} (x : _89711) (P : _89725 -> Prop) (_36520 : _89711 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) : ((term229 _89711 _89725 P f _36521 x _36520) = (term247 _89711 _89725 x P _36520 f _36521)) = ((term247 _89711 _89725 x P _36520 f _36521) = (term247 _89711 _89725 x P _36520 f _36521)).
Proof. exact (MK_COMB (@lem3460608 _89711 _89725 x P _36520 f _36521) (@lem3460626 _89711 _89725 x P _36520 f _36521)). Qed.
Lemma lem3460629 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3460630 (x : Prop) : (x = x) = True.
Proof. exact (@lem3460629 Prop x). Qed.
Lemma lem3460631 {_89711 _89725 : Type'} (x : _89711) (P : _89725 -> Prop) (_36520 : _89711 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) : ((term247 _89711 _89725 x P _36520 f _36521) = (term247 _89711 _89725 x P _36520 f _36521)) = True.
Proof. exact (@lem3460630 (term247 _89711 _89725 x P _36520 f _36521)). Qed.
Lemma lem3460632 {_89711 _89725 : Type'} (x : _89711) (P : _89725 -> Prop) (_36520 : _89711 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) : ((term229 _89711 _89725 P f _36521 x _36520) = (term247 _89711 _89725 x P _36520 f _36521)) = True.
Proof. exact (TRANS (@lem3460627 _89711 _89725 x P _36520 f _36521) (@lem3460631 _89711 _89725 x P _36520 f _36521)). Qed.
Lemma lem3460633 {_89711 _89725 : Type'} (x : _89711) (P : _89725 -> Prop) (_36520 : _89711 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) : True = ((term229 _89711 _89725 P f _36521 x _36520) = (term247 _89711 _89725 x P _36520 f _36521)).
Proof. exact (SYM (@lem3460632 _89711 _89725 x P _36520 f _36521)). Qed.
Lemma lem3460634 {_89711 _89725 : Type'} (x : _89711) (P : _89725 -> Prop) (_36520 : _89711 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) : (term229 _89711 _89725 P f _36521 x _36520) = (term247 _89711 _89725 x P _36520 f _36521).
Proof. exact (EQ_MP (@lem3460633 _89711 _89725 x P _36520 f _36521) (@lem0)). Qed.
Lemma lem3460635 {_89711 _89725 : Type'} (_36520 : _89711 -> Prop) (_36521 : _89725) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term247 _89711 _89725 x P _36520 f _36521.
Proof. exact (EQ_MP (@lem3460634 _89711 _89725 x P _36520 f _36521) (@lem3460425 _89711 _89725 _36521 _36520 P x f x' h1)). Qed.
Lemma lem3460637 (b : Prop) (a : Prop) : (a \/ b) = (term250 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3460638 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) (x : _89711) (_36520 : _89711 -> Prop) : (term247 _89711 _89725 x P _36520 f _36521) = (term251 _89711 _89725 P f _36521 x _36520).
Proof. exact (@lem3460637 (term32 _89711 _89725 P _36520 f _36521) (@IN _89711 x _36520)). Qed.
Lemma lem3460640 (a : Prop) (b : Prop) : (term252 a b) = (term253 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3460641 {_89711 _89725 : Type'} (P : _89725 -> Prop) (_36520 : _89711 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) : (term254 _89711 _89725 P _36520 f _36521) = (term255 _89711 _89725 P _36520 f _36521).
Proof. exact (@lem3460640 (term230 _89725 P _36521) (term231 _89711 _89725 _36520 f _36521)). Qed.
Lemma lem3460643 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3460644 {_89725 : Type'} (P : _89725 -> Prop) (_36521 : _89725) : (term256 _89725 P _36521) = (P _36521).
Proof. exact (@lem3460643 (P _36521)). Qed.
Lemma lem3460645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3460646 {_89725 : Type'} (P : _89725 -> Prop) (_36521 : _89725) : (term257 _89725 P _36521) = (term258 _89725 P _36521).
Proof. exact (MK_COMB (@lem3460645) (@lem3460644 _89725 P _36521)). Qed.
Lemma lem3460648 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3460649 {_89711 _89725 : Type'} (_36520 : _89711 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) : (term259 _89711 _89725 _36520 f _36521) = (_36520 = (f _36521)).
Proof. exact (@lem3460648 (_36520 = (f _36521))). Qed.
Lemma lem3460650 {_89711 _89725 : Type'} (P : _89725 -> Prop) (_36520 : _89711 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) : (term255 _89711 _89725 P _36520 f _36521) = (term20 _89711 _89725 P _36520 f _36521).
Proof. exact (MK_COMB (@lem3460646 _89725 P _36521) (@lem3460649 _89711 _89725 _36520 f _36521)). Qed.
Lemma lem3460651 {_89711 _89725 : Type'} (P : _89725 -> Prop) (_36520 : _89711 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) : (term254 _89711 _89725 P _36520 f _36521) = (term20 _89711 _89725 P _36520 f _36521).
Proof. exact (TRANS (@lem3460641 _89711 _89725 P _36520 f _36521) (@lem3460650 _89711 _89725 P _36520 f _36521)). Qed.
Lemma lem3460652 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3460653 {_89711 _89725 : Type'} (P : _89725 -> Prop) (_36520 : _89711 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) : (term260 _89711 _89725 P _36520 f _36521) = (term261 _89711 _89725 P _36520 f _36521).
Proof. exact (MK_COMB (@lem3460652) (@lem3460651 _89711 _89725 P _36520 f _36521)). Qed.
Lemma lem3460654 {_89711 : Type'} (x : _89711) (_36520 : _89711 -> Prop) : (@IN _89711 x _36520) = (@IN _89711 x _36520).
Proof. exact (eq_refl (@IN _89711 x _36520)). Qed.
Lemma lem3460655 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) (x : _89711) (_36520 : _89711 -> Prop) : (term251 _89711 _89725 P f _36521 x _36520) = (term262 _89711 _89725 P f _36521 x _36520).
Proof. exact (MK_COMB (@lem3460653 _89711 _89725 P _36520 f _36521) (@lem3460654 _89711 x _36520)). Qed.
Lemma lem3460656 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (_36521 : _89725) (x : _89711) (_36520 : _89711 -> Prop) : (term247 _89711 _89725 x P _36520 f _36521) = (term262 _89711 _89725 P f _36521 x _36520).
Proof. exact (TRANS (@lem3460638 _89711 _89725 P f _36521 x _36520) (@lem3460655 _89711 _89725 P f _36521 x _36520)). Qed.
Lemma lem3460658 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term263 _89711 _89725 P f x'.
Proof. exact (conj (@lem3460548 _89711 _89725 P x f x' h1) (@lem3460557 _89711 _89725 f x')). Qed.
Lemma lem3460660 {_89711 _89725 : Type'} (_36521 : _89725) (_36520 : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term262 _89711 _89725 P f _36521 x _36520.
Proof. exact (EQ_MP (@lem3460656 _89711 _89725 P f _36521 x _36520) (@lem3460635 _89711 _89725 _36520 _36521 P x f x' h1)). Qed.
Lemma lem3460661 {_89711 _89725 : Type'} (_36521 : _89725) (_36520 : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term262 _89711 _89725 P f _36521 x _36520.
Proof. exact (@lem3460660 _89711 _89725 _36521 _36520 P x f x' h1). Qed.
Lemma lem3460662 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term264 _89711 _89725 P x f x'.
Proof. exact (@lem3460661 _89711 _89725 x' (f x') P x f x' h1). Qed.
Lemma lem3460665 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term63 _89711 _89725 x f x'.
Proof. exact (@lem3460662 _89711 _89725 P x f x' h1 (@lem3460658 _89711 _89725 P x f x' h1)). Qed.
Lemma lem3460666 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term265 _89711 _89725 x f x'.
Proof. exact (fun h0 : term232 _89711 _89725 x f x' => @lem3460665 _89711 _89725 P x f x' h1). Qed.
Lemma lem3460668 (p : Prop) : (term239 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3460669 {_89711 _89725 : Type'} (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term265 _89711 _89725 x f x') = (term63 _89711 _89725 x f x').
Proof. exact (@lem3460668 (term63 _89711 _89725 x f x')). Qed.
Lemma lem3460670 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term63 _89711 _89725 x f x'.
Proof. exact (EQ_MP (@lem3460669 _89711 _89725 x f x') (@lem3460666 _89711 _89725 P x f x' h1)). Qed.
Lemma lem3460673 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3460675 {_89711 _89725 : Type'} (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) : (term232 _89711 _89725 x f x') = (term266 _89711 _89725 x f x').
Proof. exact (@lem3460673 (term63 _89711 _89725 x f x')). Qed.
Lemma lem3460678 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term266 _89711 _89725 x f x'.
Proof. exact (EQ_MP (@lem3460675 _89711 _89725 x f x') (@lem3460429 _89711 _89725 P x f x' h1)). Qed.
Lemma lem3460681 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : False.
Proof. exact (@lem3460678 _89711 _89725 P x f x' h1 (@lem3460670 _89711 _89725 P x f x' h1)). Qed.
Lemma lem3460682 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : term267.
Proof. exact (fun h0 : ~ False => @lem3460681 _89711 _89725 P x f x' h1). Qed.
Lemma lem3460684 (p : Prop) : (term239 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3460685 : term267 = False.
Proof. exact (@lem3460684 False). Qed.
Lemma lem3460686 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (x' : _89725) (h1 : term98 _89711 _89725 P x f x') : False.
Proof. exact (EQ_MP (@lem3460685) (@lem3460682 _89711 _89725 P x f x' h1)). Qed.
Lemma lem3460688 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : P x''.
Proof. exact (proj1 (@lem3460321 _89711 _89725 x'' t P x f h1)). Qed.
Lemma lem3460689 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term238 _89725 P x''.
Proof. exact (fun h0 : term230 _89725 P x'' => @lem3460688 _89711 _89725 x'' t P x f h1). Qed.
Lemma lem3460691 (p : Prop) : (term239 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3460692 {_89725 : Type'} (P : _89725 -> Prop) (x'' : _89725) : (term238 _89725 P x'') = (P x'').
Proof. exact (@lem3460691 (P x'')). Qed.
Lemma lem3460693 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : P x''.
Proof. exact (EQ_MP (@lem3460692 _89725 P x'') (@lem3460689 _89711 _89725 x'' t P x f h1)). Qed.
Lemma lem3460699 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3460700 {_89711 _89725 : Type'} (x : _89711) (f : type1470 _89711 _89725) (P : _89725 -> Prop) (_36522 : _89725) : (term64 _89711 _89725 P x f _36522) = (term268 _89711 _89725 x f P _36522).
Proof. exact (@lem3460699 (term63 _89711 _89725 x f _36522) (term230 _89725 P _36522)). Qed.
Lemma lem3460706 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3460707 {_89711 _89725 : Type'} (x : _89711) (f : type1470 _89711 _89725) (P : _89725 -> Prop) (_36522 : _89725) : (term269 _89711 _89725 P x f _36522) = (term270 _89711 _89725 x f P _36522).
Proof. exact (MK_COMB (@lem3460706) (@lem3460700 _89711 _89725 x f P _36522)). Qed.
Lemma lem3460713 {_89711 _89725 : Type'} (x : _89711) (f : type1470 _89711 _89725) (P : _89725 -> Prop) (_36522 : _89725) : (term268 _89711 _89725 x f P _36522) = (term268 _89711 _89725 x f P _36522).
Proof. exact (eq_refl (term268 _89711 _89725 x f P _36522)). Qed.
Lemma lem3460714 {_89711 _89725 : Type'} (x : _89711) (f : type1470 _89711 _89725) (P : _89725 -> Prop) (_36522 : _89725) : ((term64 _89711 _89725 P x f _36522) = (term268 _89711 _89725 x f P _36522)) = ((term268 _89711 _89725 x f P _36522) = (term268 _89711 _89725 x f P _36522)).
Proof. exact (MK_COMB (@lem3460707 _89711 _89725 x f P _36522) (@lem3460713 _89711 _89725 x f P _36522)). Qed.
Lemma lem3460716 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3460717 (x : Prop) : (x = x) = True.
Proof. exact (@lem3460716 Prop x). Qed.
Lemma lem3460718 {_89711 _89725 : Type'} (x : _89711) (f : type1470 _89711 _89725) (P : _89725 -> Prop) (_36522 : _89725) : ((term268 _89711 _89725 x f P _36522) = (term268 _89711 _89725 x f P _36522)) = True.
Proof. exact (@lem3460717 (term268 _89711 _89725 x f P _36522)). Qed.
Lemma lem3460719 {_89711 _89725 : Type'} (x : _89711) (f : type1470 _89711 _89725) (P : _89725 -> Prop) (_36522 : _89725) : ((term64 _89711 _89725 P x f _36522) = (term268 _89711 _89725 x f P _36522)) = True.
Proof. exact (TRANS (@lem3460714 _89711 _89725 x f P _36522) (@lem3460718 _89711 _89725 x f P _36522)). Qed.
Lemma lem3460720 {_89711 _89725 : Type'} (x : _89711) (f : type1470 _89711 _89725) (P : _89725 -> Prop) (_36522 : _89725) : True = ((term64 _89711 _89725 P x f _36522) = (term268 _89711 _89725 x f P _36522)).
Proof. exact (SYM (@lem3460719 _89711 _89725 x f P _36522)). Qed.
Lemma lem3460721 {_89711 _89725 : Type'} (x : _89711) (f : type1470 _89711 _89725) (P : _89725 -> Prop) (_36522 : _89725) : (term64 _89711 _89725 P x f _36522) = (term268 _89711 _89725 x f P _36522).
Proof. exact (EQ_MP (@lem3460720 _89711 _89725 x f P _36522) (@lem0)). Qed.
Lemma lem3460722 {_89711 _89725 : Type'} (_36522 : _89725) (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term268 _89711 _89725 x f P _36522.
Proof. exact (EQ_MP (@lem3460721 _89711 _89725 x f P _36522) (@lem3460469 _89711 _89725 _36522 x'' t P x f h1)). Qed.
Lemma lem3460724 (b : Prop) (a : Prop) : (a \/ b) = (term250 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3460725 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (_36522 : _89725) : (term268 _89711 _89725 x f P _36522) = (term271 _89711 _89725 P x f _36522).
Proof. exact (@lem3460724 (term230 _89725 P _36522) (term63 _89711 _89725 x f _36522)). Qed.
Lemma lem3460727 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3460728 {_89725 : Type'} (P : _89725 -> Prop) (_36522 : _89725) : (term256 _89725 P _36522) = (P _36522).
Proof. exact (@lem3460727 (P _36522)). Qed.
Lemma lem3460729 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3460730 {_89725 : Type'} (P : _89725 -> Prop) (_36522 : _89725) : (term272 _89725 P _36522) = (term273 _89725 P _36522).
Proof. exact (MK_COMB (@lem3460729) (@lem3460728 _89725 P _36522)). Qed.
Lemma lem3460731 {_89711 _89725 : Type'} (x : _89711) (f : type1470 _89711 _89725) (_36522 : _89725) : (term63 _89711 _89725 x f _36522) = (term63 _89711 _89725 x f _36522).
Proof. exact (eq_refl (term63 _89711 _89725 x f _36522)). Qed.
Lemma lem3460732 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (_36522 : _89725) : (term271 _89711 _89725 P x f _36522) = (term17 _89711 _89725 P x f _36522).
Proof. exact (MK_COMB (@lem3460730 _89725 P _36522) (@lem3460731 _89711 _89725 x f _36522)). Qed.
Lemma lem3460733 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (_36522 : _89725) : (term268 _89711 _89725 x f P _36522) = (term17 _89711 _89725 P x f _36522).
Proof. exact (TRANS (@lem3460725 _89711 _89725 P x f _36522) (@lem3460732 _89711 _89725 P x f _36522)). Qed.
Lemma lem3460736 {_89711 _89725 : Type'} (_36522 : _89725) (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term17 _89711 _89725 P x f _36522.
Proof. exact (EQ_MP (@lem3460733 _89711 _89725 P x f _36522) (@lem3460722 _89711 _89725 _36522 x'' t P x f h1)). Qed.
Lemma lem3460737 {_89711 _89725 : Type'} (_36522 : _89725) (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term17 _89711 _89725 P x f _36522.
Proof. exact (@lem3460736 _89711 _89725 _36522 x'' t P x f h1). Qed.
Lemma lem3460738 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term17 _89711 _89725 P x f x''.
Proof. exact (@lem3460737 _89711 _89725 x'' x'' t P x f h1). Qed.
Lemma lem3460741 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term63 _89711 _89725 x f x''.
Proof. exact (@lem3460738 _89711 _89725 x'' t P x f h1 (@lem3460693 _89711 _89725 x'' t P x f h1)). Qed.
Lemma lem3460742 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term265 _89711 _89725 x f x''.
Proof. exact (fun h0 : term232 _89711 _89725 x f x'' => @lem3460741 _89711 _89725 x'' t P x f h1). Qed.
Lemma lem3460744 (p : Prop) : (term239 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3460745 {_89711 _89725 : Type'} (x : _89711) (f : type1470 _89711 _89725) (x'' : _89725) : (term265 _89711 _89725 x f x'') = (term63 _89711 _89725 x f x'').
Proof. exact (@lem3460744 (term63 _89711 _89725 x f x'')). Qed.
Lemma lem3460746 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term63 _89711 _89725 x f x''.
Proof. exact (EQ_MP (@lem3460745 _89711 _89725 x f x'') (@lem3460742 _89711 _89725 x'' t P x f h1)). Qed.
Lemma lem3460749 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3460751 {_89711 _89725 : Type'} (x : _89711) (f : type1470 _89711 _89725) (x'' : _89725) : (term232 _89711 _89725 x f x'') = (term266 _89711 _89725 x f x'').
Proof. exact (@lem3460749 (term63 _89711 _89725 x f x'')). Qed.
Lemma lem3460754 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term266 _89711 _89725 x f x''.
Proof. exact (EQ_MP (@lem3460751 _89711 _89725 x f x'') (@lem3460482 _89711 _89725 x'' t P x f h1)). Qed.
Lemma lem3460757 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : False.
Proof. exact (@lem3460754 _89711 _89725 x'' t P x f h1 (@lem3460746 _89711 _89725 x'' t P x f h1)). Qed.
Lemma lem3460758 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : term267.
Proof. exact (fun h0 : ~ False => @lem3460757 _89711 _89725 x'' t P x f h1). Qed.
Lemma lem3460760 (p : Prop) : (term239 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3460761 : term267 = False.
Proof. exact (@lem3460760 False). Qed.
Lemma lem3460763 {_89711 _89725 : Type'} (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term151 _89711 _89725 x'' t P x f) : False.
Proof. exact (EQ_MP (@lem3460761) (@lem3460758 _89711 _89725 x'' t P x f h1)). Qed.
Lemma lem3460764 {_89711 _89725 : Type'} (x' : _89725) (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term199 _89711 _89725 x' x'' t P x f) : False.
Proof. exact (or_elim (@lem3460311 _89711 _89725 x' x'' t P x f h1) (fun h0 : term98 _89711 _89725 P x f x' => @lem3460686 _89711 _89725 P x f x' h0) (fun h0 : term151 _89711 _89725 x'' t P x f => @lem3460763 _89711 _89725 x'' t P x f h0)). Qed.
Lemma lem3460765 {_89711 _89725 : Type'} (x' : _89725) (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term199 _89711 _89725 x' x'' t P x f) : (term199 _89711 _89725 x' x'' t P x f) = False.
Proof. exact (prop_ext (fun h2 : term199 _89711 _89725 x' x'' t P x f => @lem3460764 _89711 _89725 x' x'' t P x f h1) (fun h2 : False => @lem3460311 _89711 _89725 x' x'' t P x f h1)). Qed.
Lemma lem3460766 {_89711 _89725 : Type'} (x' : _89725) (x'' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term199 _89711 _89725 x' x'' t P x f) : False.
Proof. exact (EQ_MP (@lem3460765 _89711 _89725 x' x'' t P x f h1) (@lem3460311 _89711 _89725 x' x'' t P x f h1)). Qed.
Lemma lem3460767 {_89711 _89725 : Type'} (x' : _89725) (t : _89711 -> Prop) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term202 _89711 _89725 x' t P x f) : False.
Proof. exact (ex_elim (@lem3460213 _89711 _89725 x' t P x f h1) (fun x'' : _89725 => fun h0 : term201 _89711 _89725 x' t P x f x'' => @lem3460766 _89711 _89725 x' x'' t P x f h0)). Qed.
Lemma lem3460768 {_89711 _89725 : Type'} (x' : _89725) (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term204 _89711 _89725 x' P x f) : False.
Proof. exact (ex_elim (@lem3460212 _89711 _89725 x' P x f h1) (fun t : _89711 -> Prop => fun h0 : term203 _89711 _89725 x' P x f t => @lem3460767 _89711 _89725 x' t P x f h0)). Qed.
Lemma lem3460769 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term30 _89711 _89725 P x f) : False.
Proof. exact (ex_elim (@lem3460211 _89711 _89725 P x f h1) (fun x' : _89725 => fun h0 : term205 _89711 _89725 P x f x' => @lem3460768 _89711 _89725 x' P x f h0)). Qed.
Lemma lem3460770 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term30 _89711 _89725 P x f) : (term30 _89711 _89725 P x f) = False.
Proof. exact (prop_ext (fun h2 : term30 _89711 _89725 P x f => @lem3460769 _89711 _89725 P x f h1) (fun h2 : False => @lem3459689 _89711 _89725 P x f h1)). Qed.
Lemma lem3460771 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) (h1 : term30 _89711 _89725 P x f) : False.
Proof. exact (EQ_MP (@lem3460770 _89711 _89725 P x f h1) (@lem3459689 _89711 _89725 P x f h1)). Qed.
Lemma lem3460772 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : term29 _89711 _89725 P x f.
Proof. exact (fun h0 : term30 _89711 _89725 P x f => @lem3460771 _89711 _89725 P x f h0). Qed.
Lemma lem3460773 {_89711 _89725 : Type'} (P : _89725 -> Prop) (x : _89711) (f : type1470 _89711 _89725) : (term26 _89711 _89725 P f x) = (term19 _89711 _89725 P x f).
Proof. exact (EQ_MP (@lem3459688 _89711 _89725 P x f) (@lem3460772 _89711 _89725 P x f)). Qed.
Lemma lem3460778 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term1 _89711 _89725 P f.
Proof. exact (fun x : _89711 => @lem3460773 _89711 _89725 P x f). Qed.
Lemma lem3460783 {_89711 _89725 : Type'} (f : type1470 _89711 _89725) : term12 _89711 _89725 f.
Proof. exact (fun P : _89725 -> Prop => @lem3460778 _89711 _89725 P f). Qed.
Lemma lem3460788 {_89711 _89725 : Type'} : term16 _89711 _89725.
Proof. exact (fun f : type1470 _89711 _89725 => @lem3460783 _89711 _89725 f). Qed.
Lemma lem3460789 {_89711 _89725 : Type'} : term15 _89711 _89725.
Proof. exact (EQ_MP (@lem3459684 _89711 _89725) (@lem3460788 _89711 _89725)). Qed.
Lemma lem3460790 {_89711 _89725 : Type'} (f : type1470 _89711 _89725) : term274 _89711 _89725 f.
Proof. exact (@lem3460789 _89711 _89725 f). Qed.
Lemma lem3460791 {_89711 _89725 : Type'} (f : type1470 _89711 _89725) : (term274 _89711 _89725 f) = (term11 _89711 _89725 f).
Proof. exact (eq_refl (term274 _89711 _89725 f)). Qed.
Lemma lem3460792 {_89711 _89725 : Type'} (f : type1470 _89711 _89725) : term11 _89711 _89725 f.
Proof. exact (EQ_MP (@lem3460791 _89711 _89725 f) (@lem3460790 _89711 _89725 f)). Qed.
Lemma lem3460793 {_89711 _89725 : Type'} (f : type1470 _89711 _89725) (P : _89725 -> Prop) : term275 _89711 _89725 f P.
Proof. exact (@lem3460792 _89711 _89725 f P). Qed.
Lemma lem3460794 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term275 _89711 _89725 f P) = (term2 _89711 _89725 P f).
Proof. exact (eq_refl (term275 _89711 _89725 f P)). Qed.
Lemma lem3460795 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term2 _89711 _89725 P f.
Proof. exact (EQ_MP (@lem3460794 _89711 _89725 P f) (@lem3460793 _89711 _89725 f P)). Qed.
Lemma lem3460797 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term2 _89711 _89725 P f.
Proof. exact (@lem3459524 _89711 _89725 P f (@lem3460795 _89711 _89725 P f)). Qed.
Lemma lem3460798 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (h1 : term3 _89711 _89725 P f) : False.
Proof. exact (@lem3460797 _89711 _89725 P f (@lem3459508 _89711 _89725 P f h1)). Qed.
Lemma lem3460799 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (h1 : term3 _89711 _89725 P f) : (term3 _89711 _89725 P f) = False.
Proof. exact (prop_ext (fun h2 : term3 _89711 _89725 P f => @lem3460798 _89711 _89725 P f h1) (fun h2 : False => @lem3459508 _89711 _89725 P f h1)). Qed.
Lemma lem3460800 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) (h1 : term3 _89711 _89725 P f) : False.
Proof. exact (EQ_MP (@lem3460799 _89711 _89725 P f h1) (@lem3459508 _89711 _89725 P f h1)). Qed.
Lemma lem3460801 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term2 _89711 _89725 P f.
Proof. exact (fun h0 : term3 _89711 _89725 P f => @lem3460800 _89711 _89725 P f h0). Qed.
Lemma lem3460802 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term1 _89711 _89725 P f.
Proof. exact (EQ_MP (@lem3459507 _89711 _89725 P f) (@lem3460801 _89711 _89725 P f)). Qed.
