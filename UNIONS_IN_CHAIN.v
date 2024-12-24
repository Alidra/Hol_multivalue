Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_IN_CHAIN_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_INDUCT_spec.
Require Import FORALL_AND_THM_spec.
Require Import FORALL_IN_INSERT_spec.
Require Import IN_INSERT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_INSERT_EMPTY_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import UNION_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3322101_spec.
Require Import thm3322164_spec.
Require Import thm3324017_spec.
Require Import thm3325374_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem3756521 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3756522 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : (term1 _98208 s t f) = (term2 _98208 s t f).
Proof. exact (@lem3756521 (term1 _98208 s t f)). Qed.
Lemma lem3756523 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : (term2 _98208 s t f) = (term1 _98208 s t f).
Proof. exact (SYM (@lem3756522 _98208 s t f)). Qed.
Lemma lem3756524 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term3 _98208 s t f) : term3 _98208 s t f.
Proof. exact (h1). Qed.
Lemma lem3756527 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term2 _98208 s t f) : term2 _98208 s t f.
Proof. exact (h1). Qed.
Lemma lem3756528 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : term4 _98208 s t f.
Proof. exact (fun h0 : term2 _98208 s t f => @lem3756527 _98208 s t f h0). Qed.
Lemma lem3756529 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term4 _98208 s t f) : term4 _98208 s t f.
Proof. exact (h1). Qed.
Lemma lem3756530 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term2 _98208 s t f) : term2 _98208 s t f.
Proof. exact (h1). Qed.
Lemma lem3756531 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term2 _98208 s t f) (h2 : term4 _98208 s t f) : term2 _98208 s t f.
Proof. exact (@lem3756529 _98208 s t f h2 (@lem3756530 _98208 s t f h1)). Qed.
Lemma lem3756532 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term2 _98208 s t f) : term5 _98208 s t f.
Proof. exact (fun h0 : term4 _98208 s t f => @lem3756531 _98208 s t f h1 h0). Qed.
Lemma lem3756533 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term4 _98208 s t f) : term4 _98208 s t f.
Proof. exact (h1). Qed.
Lemma lem3756534 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term2 _98208 s t f) (h2 : term4 _98208 s t f) : term2 _98208 s t f.
Proof. exact (@lem3756532 _98208 s t f h1 (@lem3756533 _98208 s t f h2)). Qed.
Lemma lem3756535 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term4 _98208 s t f) : term4 _98208 s t f.
Proof. exact (fun h0 : term2 _98208 s t f => @lem3756534 _98208 s t f h0 h1). Qed.
Lemma lem3756536 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : term6 _98208 s t f.
Proof. exact (fun h0 : term4 _98208 s t f => @lem3756535 _98208 s t f h0). Qed.
Lemma lem3756539 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : term4 _98208 s t f.
Proof. exact (@lem3756536 _98208 s t f (@lem3756528 _98208 s t f)). Qed.
Lemma lem3756540 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : term4 _98208 s t f.
Proof. exact (@lem3756539 _98208 s t f). Qed.
Lemma lem3756554 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3756555 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : (term2 _98208 s t f) = (term7 _98208 s t f).
Proof. exact (@lem3756554 (term3 _98208 s t f)). Qed.
Lemma lem3756557 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3756558 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : (term7 _98208 s t f) = (term1 _98208 s t f).
Proof. exact (@lem3756557 (term1 _98208 s t f)). Qed.
Lemma lem3756561 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : (term2 _98208 s t f) = (term1 _98208 s t f).
Proof. exact (TRANS (@lem3756555 _98208 s t f) (@lem3756558 _98208 s t f)). Qed.
Lemma lem3756568 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) : (term9 _98208 t f) = (term10 _98208 t f).
Proof. exact (fun_ext (fun s : _98208 -> Prop => @lem3756561 _98208 s t f)). Qed.
Lemma lem3756569 {_98208 : Type'} : (@all (_98208 -> Prop)) = (@all (_98208 -> Prop)).
Proof. exact (eq_refl (@all (_98208 -> Prop))). Qed.
Lemma lem3756570 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) : (term11 _98208 t f) = (term12 _98208 t f).
Proof. exact (MK_COMB (@lem3756569 _98208) (@lem3756568 _98208 t f)). Qed.
Lemma lem3756575 {_98208 : Type'} (f : type686 _98208) : (term13 _98208 f) = (term14 _98208 f).
Proof. exact (fun_ext (fun t : _98208 -> Prop => @lem3756570 _98208 t f)). Qed.
Lemma lem3756576 {_98208 : Type'} : (@all (_98208 -> Prop)) = (@all (_98208 -> Prop)).
Proof. exact (eq_refl (@all (_98208 -> Prop))). Qed.
Lemma lem3756577 {_98208 : Type'} (f : type686 _98208) : (term15 _98208 f) = (term16 _98208 f).
Proof. exact (MK_COMB (@lem3756576 _98208) (@lem3756575 _98208 f)). Qed.
Lemma lem3756582 {_98208 : Type'} : (term17 _98208) = (term18 _98208).
Proof. exact (fun_ext (fun f : type686 _98208 => @lem3756577 _98208 f)). Qed.
Lemma lem3756583 {_98208 : Type'} : (@all ((_98208 -> Prop) -> Prop)) = (@all ((_98208 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_98208 -> Prop) -> Prop))). Qed.
Lemma lem3756592 {_98208 : Type'} : (term19 _98208) = (term20 _98208).
Proof. exact (MK_COMB (@lem3756583 _98208) (@lem3756582 _98208)). Qed.
Lemma lem3756609 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : (term1 _98208 s t f) = (term1 _98208 s t f).
Proof. exact (eq_refl (term1 _98208 s t f)). Qed.
Lemma lem3756610 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) : (term10 _98208 t f) = (term10 _98208 t f).
Proof. exact (fun_ext (fun s : _98208 -> Prop => @lem3756609 _98208 s t f)). Qed.
Lemma lem3756611 {_98208 : Type'} : (@all (_98208 -> Prop)) = (@all (_98208 -> Prop)).
Proof. exact (eq_refl (@all (_98208 -> Prop))). Qed.
Lemma lem3756612 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) : (term12 _98208 t f) = (term12 _98208 t f).
Proof. exact (MK_COMB (@lem3756611 _98208) (@lem3756610 _98208 t f)). Qed.
Lemma lem3756613 {_98208 : Type'} (f : type686 _98208) : (term14 _98208 f) = (term14 _98208 f).
Proof. exact (fun_ext (fun t : _98208 -> Prop => @lem3756612 _98208 t f)). Qed.
Lemma lem3756614 {_98208 : Type'} : (@all (_98208 -> Prop)) = (@all (_98208 -> Prop)).
Proof. exact (eq_refl (@all (_98208 -> Prop))). Qed.
Lemma lem3756615 {_98208 : Type'} (f : type686 _98208) : (term16 _98208 f) = (term16 _98208 f).
Proof. exact (MK_COMB (@lem3756614 _98208) (@lem3756613 _98208 f)). Qed.
Lemma lem3756616 {_98208 : Type'} : (term18 _98208) = (term18 _98208).
Proof. exact (fun_ext (fun f : type686 _98208 => @lem3756615 _98208 f)). Qed.
Lemma lem3756617 {_98208 : Type'} : (@all ((_98208 -> Prop) -> Prop)) = (@all ((_98208 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_98208 -> Prop) -> Prop))). Qed.
Lemma lem3756618 {_98208 : Type'} : (term20 _98208) = (term20 _98208).
Proof. exact (MK_COMB (@lem3756617 _98208) (@lem3756616 _98208)). Qed.
Lemma lem3756647 {_98208 : Type'} : (term19 _98208) = (term20 _98208).
Proof. exact (TRANS (@lem3756592 _98208) (@lem3756618 _98208)). Qed.
Lemma lem3756648 {_98208 : Type'} : (term20 _98208) = (term19 _98208).
Proof. exact (SYM (@lem3756647 _98208)). Qed.
Lemma lem3756652 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3756653 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : (term21 _98208 s t f) = (term22 _98208 s t f).
Proof. exact (@lem3756652 (term21 _98208 s t f)). Qed.
Lemma lem3756654 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : (term22 _98208 s t f) = (term21 _98208 s t f).
Proof. exact (SYM (@lem3756653 _98208 s t f)). Qed.
Lemma lem3756655 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) : term23 _98208 s t f.
Proof. exact (h1). Qed.
Lemma lem3756665 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term24 _98208 s t) : term24 _98208 s t.
Proof. exact (h1). Qed.
Lemma lem3756671 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) (h1 : @IN (_98208 -> Prop) t f) : @IN (_98208 -> Prop) t f.
Proof. exact (h1). Qed.
Lemma lem3756682 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : (term23 _98208 s t f) = (term25 _98208 s t f).
Proof. exact (@lem17160 ((@UNION _98208 s t) = s) (term26 _98208 s t f)). Qed.
Lemma lem3756705 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term24 _98208 s t) : term24 _98208 s t.
Proof. exact (h1). Qed.
Lemma lem3756711 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) (h1 : @IN (_98208 -> Prop) t f) : @IN (_98208 -> Prop) t f.
Proof. exact (h1). Qed.
Lemma lem3756737 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) : term25 _98208 s t f.
Proof. exact (EQ_MP (@lem3756682 _98208 s t f) (@lem3756655 _98208 s t f h1)). Qed.
Lemma lem3756757 {_98208 : Type'} (t : _98208 -> Prop) (s : _98208 -> Prop) (h1 : (@UNION _98208 s t) = s) : (@UNION _98208 s t) = s.
Proof. exact (h1). Qed.
Lemma lem3756761 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) (h1 : @IN (_98208 -> Prop) t f) : @IN (_98208 -> Prop) t f.
Proof. exact (h1). Qed.
Lemma lem3756773 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : (@UNION _98208 s t) = t) : (@UNION _98208 s t) = t.
Proof. exact (h1). Qed.
Lemma lem3756777 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) : term27 _98208 t s.
Proof. exact (proj1 (@lem3756737 _98208 s t f h1)). Qed.
Lemma lem3756781 {_98208 : Type'} (t : _98208 -> Prop) (s : _98208 -> Prop) (h1 : (@UNION _98208 s t) = s) : (@UNION _98208 s t) = s.
Proof. exact (h1). Qed.
Lemma lem3756783 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) (h1 : @IN (_98208 -> Prop) t f) : @IN (_98208 -> Prop) t f.
Proof. exact (h1). Qed.
Lemma lem3756787 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) : term28 _98208 s t f.
Proof. exact (proj2 (@lem3756737 _98208 s t f h1)). Qed.
Lemma lem3756789 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : (@UNION _98208 s t) = t) : (@UNION _98208 s t) = t.
Proof. exact (h1). Qed.
Lemma lem3756829 {_98208 : Type'} (t : _98208 -> Prop) (s : _98208 -> Prop) (h1 : (@UNION _98208 s t) = s) : (@UNION _98208 s t) = s.
Proof. exact (h1). Qed.
Lemma lem3756830 {_98208 : Type'} (t : _98208 -> Prop) (s : _98208 -> Prop) (h1 : (@UNION _98208 s t) = s) : term29 _98208 t s.
Proof. exact (fun h0 : term27 _98208 t s => @lem3756829 _98208 t s h1). Qed.
Lemma lem3756832 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3756833 {_98208 : Type'} (t : _98208 -> Prop) (s : _98208 -> Prop) : (term29 _98208 t s) = ((@UNION _98208 s t) = s).
Proof. exact (@lem3756832 ((@UNION _98208 s t) = s)). Qed.
Lemma lem3756834 {_98208 : Type'} (t : _98208 -> Prop) (s : _98208 -> Prop) (h1 : (@UNION _98208 s t) = s) : (@UNION _98208 s t) = s.
Proof. exact (EQ_MP (@lem3756833 _98208 t s) (@lem3756830 _98208 t s h1)). Qed.
Lemma lem3756837 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3756839 {_98208 : Type'} (t : _98208 -> Prop) (s : _98208 -> Prop) : (term27 _98208 t s) = (term31 _98208 t s).
Proof. exact (@lem3756837 ((@UNION _98208 s t) = s)). Qed.
Lemma lem3756842 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) : term31 _98208 t s.
Proof. exact (EQ_MP (@lem3756839 _98208 t s) (@lem3756777 _98208 s t f h1)). Qed.
Lemma lem3756845 {_98208 : Type'} (f : type686 _98208) (t : _98208 -> Prop) (s : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = s) : False.
Proof. exact (@lem3756842 _98208 s t f h1 (@lem3756834 _98208 t s h2)). Qed.
Lemma lem3756846 {_98208 : Type'} (f : type686 _98208) (t : _98208 -> Prop) (s : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = s) : term32.
Proof. exact (fun h0 : ~ False => @lem3756845 _98208 f t s h1 h2). Qed.
Lemma lem3756848 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3756849 : term32 = False.
Proof. exact (@lem3756848 False). Qed.
Lemma lem3756850 {_98208 : Type'} (f : type686 _98208) (t : _98208 -> Prop) (s : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = s) : False.
Proof. exact (EQ_MP (@lem3756849) (@lem3756846 _98208 f t s h1 h2)). Qed.
Lemma lem3756851 {_98208 : Type'} : (@IN (_98208 -> Prop)) = (@IN (_98208 -> Prop)).
Proof. exact (eq_refl (@IN (_98208 -> Prop))). Qed.
Lemma lem3756852 {_98208 : Type'} (_43211 : _98208 -> Prop) (_43213 : _98208 -> Prop) (h1 : _43211 = _43213) : _43211 = _43213.
Proof. exact (h1). Qed.
Lemma lem3756853 {_98208 : Type'} (_43212 : type686 _98208) (_43214 : type686 _98208) (h1 : _43212 = _43214) : _43212 = _43214.
Proof. exact (h1). Qed.
Lemma lem3756854 {_98208 : Type'} (_43211 : _98208 -> Prop) (_43213 : _98208 -> Prop) (h1 : _43211 = _43213) : (@IN (_98208 -> Prop) _43211) = (@IN (_98208 -> Prop) _43213).
Proof. exact (MK_COMB (@lem3756851 _98208) (@lem3756852 _98208 _43211 _43213 h1)). Qed.
Lemma lem3756855 {_98208 : Type'} (_43211 : _98208 -> Prop) (_43213 : _98208 -> Prop) (_43212 : type686 _98208) (_43214 : type686 _98208) (h1 : _43211 = _43213) (h2 : _43212 = _43214) : (@IN (_98208 -> Prop) _43211 _43212) = (@IN (_98208 -> Prop) _43213 _43214).
Proof. exact (MK_COMB (@lem3756854 _98208 _43211 _43213 h1) (@lem3756853 _98208 _43212 _43214 h2)). Qed.
Lemma lem3756857 (b : Prop) (a : Prop) : term33 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3756858 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : term34 _98208 _43213 _43214 _43211 _43212.
Proof. exact (@lem3756857 (@IN (_98208 -> Prop) _43213 _43214) (@IN (_98208 -> Prop) _43211 _43212)). Qed.
Lemma lem3756859 {_98208 : Type'} (_43211 : _98208 -> Prop) (_43213 : _98208 -> Prop) (_43212 : type686 _98208) (_43214 : type686 _98208) (h1 : _43211 = _43213) (h2 : _43212 = _43214) : term35 _98208 _43213 _43214 _43211 _43212.
Proof. exact (@lem3756858 _98208 _43213 _43214 _43211 _43212 (@lem3756855 _98208 _43211 _43213 _43212 _43214 h1 h2)). Qed.
Lemma lem3756860 {_98208 : Type'} (_43214 : type686 _98208) (_43212 : type686 _98208) (_43211 : _98208 -> Prop) (_43213 : _98208 -> Prop) (h1 : _43211 = _43213) : term36 _98208 _43213 _43214 _43211 _43212.
Proof. exact (fun h0 : _43212 = _43214 => @lem3756859 _98208 _43211 _43213 _43212 _43214 h1 h0). Qed.
Lemma lem3756862 (a : Prop) (b : Prop) : (a -> b) = (term37 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3756863 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term36 _98208 _43213 _43214 _43211 _43212) = (term38 _98208 _43213 _43214 _43211 _43212).
Proof. exact (@lem3756862 (_43212 = _43214) (term35 _98208 _43213 _43214 _43211 _43212)). Qed.
Lemma lem3756864 {_98208 : Type'} (_43214 : type686 _98208) (_43212 : type686 _98208) (_43211 : _98208 -> Prop) (_43213 : _98208 -> Prop) (h1 : _43211 = _43213) : term38 _98208 _43213 _43214 _43211 _43212.
Proof. exact (EQ_MP (@lem3756863 _98208 _43213 _43214 _43211 _43212) (@lem3756860 _98208 _43214 _43212 _43211 _43213 h1)). Qed.
Lemma lem3756865 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : term39 _98208 _43213 _43214 _43211 _43212.
Proof. exact (fun h0 : _43211 = _43213 => @lem3756864 _98208 _43214 _43212 _43211 _43213 h0). Qed.
Lemma lem3756867 (a : Prop) (b : Prop) : (a -> b) = (term37 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3756868 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term39 _98208 _43213 _43214 _43211 _43212) = (term40 _98208 _43213 _43214 _43211 _43212).
Proof. exact (@lem3756867 (_43211 = _43213) (term38 _98208 _43213 _43214 _43211 _43212)). Qed.
Lemma lem3756869 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : term40 _98208 _43213 _43214 _43211 _43212.
Proof. exact (EQ_MP (@lem3756868 _98208 _43213 _43214 _43211 _43212) (@lem3756865 _98208 _43213 _43214 _43211 _43212)). Qed.
Lemma lem3756886 {_98208 : Type'} (x : _98208 -> Prop) (y : _98208 -> Prop) (z : _98208 -> Prop) : term41 _98208 x y z.
Proof. exact (@lem21385 (_98208 -> Prop) x y z). Qed.
Lemma lem3756890 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : (@UNION _98208 s t) = t) : (@UNION _98208 s t) = t.
Proof. exact (h1). Qed.
Lemma lem3756891 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : (@UNION _98208 s t) = t) : term42 _98208 s t.
Proof. exact (fun h0 : term43 _98208 s t => @lem3756890 _98208 s t h1). Qed.
Lemma lem3756893 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3756894 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) : (term42 _98208 s t) = ((@UNION _98208 s t) = t).
Proof. exact (@lem3756893 ((@UNION _98208 s t) = t)). Qed.
Lemma lem3756895 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : (@UNION _98208 s t) = t) : (@UNION _98208 s t) = t.
Proof. exact (EQ_MP (@lem3756894 _98208 s t) (@lem3756891 _98208 s t h1)). Qed.
Lemma lem3756897 {_98208 : Type'} (x : _98208 -> Prop) : x = x.
Proof. exact (@lem21386 (_98208 -> Prop) x). Qed.
Lemma lem3756898 {_98208 : Type'} (x : _98208 -> Prop) : x = x.
Proof. exact (@lem3756897 _98208 x). Qed.
Lemma lem3756899 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) : (@UNION _98208 s t) = (@UNION _98208 s t).
Proof. exact (@lem3756898 _98208 (@UNION _98208 s t)). Qed.
Lemma lem3756900 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) : term44 _98208 s t.
Proof. exact (fun h0 : term45 _98208 s t => @lem3756899 _98208 s t). Qed.
Lemma lem3756902 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3756903 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) : (term44 _98208 s t) = ((@UNION _98208 s t) = (@UNION _98208 s t)).
Proof. exact (@lem3756902 ((@UNION _98208 s t) = (@UNION _98208 s t))). Qed.
Lemma lem3756904 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) : (@UNION _98208 s t) = (@UNION _98208 s t).
Proof. exact (EQ_MP (@lem3756903 _98208 s t) (@lem3756900 _98208 s t)). Qed.
Lemma lem3756922 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3756923 {_98208 : Type'} (y : _98208 -> Prop) (x : _98208 -> Prop) (z : _98208 -> Prop) : (term46 _98208 x y z) = (term47 _98208 y x z).
Proof. exact (@lem3756922 (y = z) (term48 _98208 x z)). Qed.
Lemma lem3756933 {_98208 : Type'} (x : _98208 -> Prop) (y : _98208 -> Prop) : (term49 _98208 x y) = (term49 _98208 x y).
Proof. exact (eq_refl (term49 _98208 x y)). Qed.
Lemma lem3756934 {_98208 : Type'} (y : _98208 -> Prop) (x : _98208 -> Prop) (z : _98208 -> Prop) : (term41 _98208 x y z) = (term50 _98208 y x z).
Proof. exact (MK_COMB (@lem3756933 _98208 x y) (@lem3756923 _98208 y x z)). Qed.
Lemma lem3756938 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3756939 {_98208 : Type'} (y : _98208 -> Prop) (x : _98208 -> Prop) (z : _98208 -> Prop) : (term50 _98208 y x z) = (term52 _98208 y x z).
Proof. exact (@lem3756938 (y = z) (term48 _98208 x y) (term48 _98208 x z)). Qed.
Lemma lem3756961 {_98208 : Type'} (y : _98208 -> Prop) (x : _98208 -> Prop) (z : _98208 -> Prop) : (term41 _98208 x y z) = (term52 _98208 y x z).
Proof. exact (TRANS (@lem3756934 _98208 y x z) (@lem3756939 _98208 y x z)). Qed.
Lemma lem3756962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3756963 {_98208 : Type'} (y : _98208 -> Prop) (x : _98208 -> Prop) (z : _98208 -> Prop) : (term53 _98208 x y z) = (term54 _98208 y x z).
Proof. exact (MK_COMB (@lem3756962) (@lem3756961 _98208 y x z)). Qed.
Lemma lem3756985 {_98208 : Type'} (y : _98208 -> Prop) (x : _98208 -> Prop) (z : _98208 -> Prop) : (term52 _98208 y x z) = (term52 _98208 y x z).
Proof. exact (eq_refl (term52 _98208 y x z)). Qed.
Lemma lem3756986 {_98208 : Type'} (y : _98208 -> Prop) (x : _98208 -> Prop) (z : _98208 -> Prop) : ((term41 _98208 x y z) = (term52 _98208 y x z)) = ((term52 _98208 y x z) = (term52 _98208 y x z)).
Proof. exact (MK_COMB (@lem3756963 _98208 y x z) (@lem3756985 _98208 y x z)). Qed.
Lemma lem3756988 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3756989 (x : Prop) : (x = x) = True.
Proof. exact (@lem3756988 Prop x). Qed.
Lemma lem3756990 {_98208 : Type'} (y : _98208 -> Prop) (x : _98208 -> Prop) (z : _98208 -> Prop) : ((term52 _98208 y x z) = (term52 _98208 y x z)) = True.
Proof. exact (@lem3756989 (term52 _98208 y x z)). Qed.
Lemma lem3756991 {_98208 : Type'} (y : _98208 -> Prop) (x : _98208 -> Prop) (z : _98208 -> Prop) : ((term41 _98208 x y z) = (term52 _98208 y x z)) = True.
Proof. exact (TRANS (@lem3756986 _98208 y x z) (@lem3756990 _98208 y x z)). Qed.
Lemma lem3756992 {_98208 : Type'} (y : _98208 -> Prop) (x : _98208 -> Prop) (z : _98208 -> Prop) : True = ((term41 _98208 x y z) = (term52 _98208 y x z)).
Proof. exact (SYM (@lem3756991 _98208 y x z)). Qed.
Lemma lem3756993 {_98208 : Type'} (y : _98208 -> Prop) (x : _98208 -> Prop) (z : _98208 -> Prop) : (term41 _98208 x y z) = (term52 _98208 y x z).
Proof. exact (EQ_MP (@lem3756992 _98208 y x z) (@lem0)). Qed.
Lemma lem3756994 {_98208 : Type'} (y : _98208 -> Prop) (x : _98208 -> Prop) (z : _98208 -> Prop) : term52 _98208 y x z.
Proof. exact (EQ_MP (@lem3756993 _98208 y x z) (@lem3756886 _98208 x y z)). Qed.
Lemma lem3756996 (b : Prop) (a : Prop) : (a \/ b) = (term55 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3756997 {_98208 : Type'} (x : _98208 -> Prop) (y : _98208 -> Prop) (z : _98208 -> Prop) : (term52 _98208 y x z) = (term56 _98208 x y z).
Proof. exact (@lem3756996 (term57 _98208 y x z) (y = z)). Qed.
Lemma lem3756999 (a : Prop) (b : Prop) : (term58 a b) = (term59 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3757000 {_98208 : Type'} (y : _98208 -> Prop) (x : _98208 -> Prop) (z : _98208 -> Prop) : (term60 _98208 y x z) = (term61 _98208 y x z).
Proof. exact (@lem3756999 (term48 _98208 x y) (term48 _98208 x z)). Qed.
Lemma lem3757002 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3757003 {_98208 : Type'} (x : _98208 -> Prop) (y : _98208 -> Prop) : (term62 _98208 x y) = (x = y).
Proof. exact (@lem3757002 (x = y)). Qed.
Lemma lem3757004 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3757005 {_98208 : Type'} (x : _98208 -> Prop) (y : _98208 -> Prop) : (term63 _98208 x y) = (term64 _98208 x y).
Proof. exact (MK_COMB (@lem3757004) (@lem3757003 _98208 x y)). Qed.
Lemma lem3757007 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3757008 {_98208 : Type'} (x : _98208 -> Prop) (z : _98208 -> Prop) : (term62 _98208 x z) = (x = z).
Proof. exact (@lem3757007 (x = z)). Qed.
Lemma lem3757009 {_98208 : Type'} (y : _98208 -> Prop) (x : _98208 -> Prop) (z : _98208 -> Prop) : (term61 _98208 y x z) = (term65 _98208 y x z).
Proof. exact (MK_COMB (@lem3757005 _98208 x y) (@lem3757008 _98208 x z)). Qed.
Lemma lem3757010 {_98208 : Type'} (y : _98208 -> Prop) (x : _98208 -> Prop) (z : _98208 -> Prop) : (term60 _98208 y x z) = (term65 _98208 y x z).
Proof. exact (TRANS (@lem3757000 _98208 y x z) (@lem3757009 _98208 y x z)). Qed.
Lemma lem3757011 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3757012 {_98208 : Type'} (y : _98208 -> Prop) (x : _98208 -> Prop) (z : _98208 -> Prop) : (term66 _98208 y x z) = (term67 _98208 y x z).
Proof. exact (MK_COMB (@lem3757011) (@lem3757010 _98208 y x z)). Qed.
Lemma lem3757013 {_98208 : Type'} (y : _98208 -> Prop) (z : _98208 -> Prop) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3757014 {_98208 : Type'} (x : _98208 -> Prop) (y : _98208 -> Prop) (z : _98208 -> Prop) : (term56 _98208 x y z) = (term68 _98208 x y z).
Proof. exact (MK_COMB (@lem3757012 _98208 y x z) (@lem3757013 _98208 y z)). Qed.
Lemma lem3757015 {_98208 : Type'} (x : _98208 -> Prop) (y : _98208 -> Prop) (z : _98208 -> Prop) : (term52 _98208 y x z) = (term68 _98208 x y z).
Proof. exact (TRANS (@lem3756997 _98208 x y z) (@lem3757014 _98208 x y z)). Qed.
Lemma lem3757017 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : (@UNION _98208 s t) = t) : term69 _98208 s t.
Proof. exact (conj (@lem3756895 _98208 s t h1) (@lem3756904 _98208 s t)). Qed.
Lemma lem3757019 {_98208 : Type'} (x : _98208 -> Prop) (y : _98208 -> Prop) (z : _98208 -> Prop) : term68 _98208 x y z.
Proof. exact (EQ_MP (@lem3757015 _98208 x y z) (@lem3756994 _98208 y x z)). Qed.
Lemma lem3757020 {_98208 : Type'} (x : _98208 -> Prop) (y : _98208 -> Prop) (z : _98208 -> Prop) : term68 _98208 x y z.
Proof. exact (@lem3757019 _98208 x y z). Qed.
Lemma lem3757021 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) : term70 _98208 s t.
Proof. exact (@lem3757020 _98208 (@UNION _98208 s t) t (@UNION _98208 s t)). Qed.
Lemma lem3757024 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : (@UNION _98208 s t) = t) : t = (@UNION _98208 s t).
Proof. exact (@lem3757021 _98208 s t (@lem3757017 _98208 s t h1)). Qed.
Lemma lem3757025 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : (@UNION _98208 s t) = t) : term71 _98208 s t.
Proof. exact (fun h0 : term72 _98208 s t => @lem3757024 _98208 s t h1). Qed.
Lemma lem3757027 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3757028 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) : (term71 _98208 s t) = (t = (@UNION _98208 s t)).
Proof. exact (@lem3757027 (t = (@UNION _98208 s t))). Qed.
Lemma lem3757029 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : (@UNION _98208 s t) = t) : t = (@UNION _98208 s t).
Proof. exact (EQ_MP (@lem3757028 _98208 s t) (@lem3757025 _98208 s t h1)). Qed.
Lemma lem3757031 {_98208 : Type'} (x : type686 _98208) : x = x.
Proof. exact (@lem21386 (type686 _98208) x). Qed.
Lemma lem3757032 {_98208 : Type'} (x : type686 _98208) : x = x.
Proof. exact (@lem3757031 _98208 x). Qed.
Lemma lem3757033 {_98208 : Type'} (f : type686 _98208) : f = f.
Proof. exact (@lem3757032 _98208 f). Qed.
Lemma lem3757034 {_98208 : Type'} (f : type686 _98208) : term73 _98208 f.
Proof. exact (fun h0 : term74 _98208 f => @lem3757033 _98208 f). Qed.
Lemma lem3757036 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3757037 {_98208 : Type'} (f : type686 _98208) : (term73 _98208 f) = (f = f).
Proof. exact (@lem3757036 (f = f)). Qed.
Lemma lem3757038 {_98208 : Type'} (f : type686 _98208) : f = f.
Proof. exact (EQ_MP (@lem3757037 _98208 f) (@lem3757034 _98208 f)). Qed.
Lemma lem3757040 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) (h1 : @IN (_98208 -> Prop) t f) : @IN (_98208 -> Prop) t f.
Proof. exact (h1). Qed.
Lemma lem3757041 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) (h1 : @IN (_98208 -> Prop) t f) : term75 _98208 t f.
Proof. exact (fun h0 : term76 _98208 t f => @lem3757040 _98208 t f h1). Qed.
Lemma lem3757043 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3757044 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) : (term75 _98208 t f) = (@IN (_98208 -> Prop) t f).
Proof. exact (@lem3757043 (@IN (_98208 -> Prop) t f)). Qed.
Lemma lem3757045 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) (h1 : @IN (_98208 -> Prop) t f) : @IN (_98208 -> Prop) t f.
Proof. exact (EQ_MP (@lem3757044 _98208 t f) (@lem3757041 _98208 t f h1)). Qed.
Lemma lem3757063 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3757064 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term38 _98208 _43213 _43214 _43211 _43212) = (term77 _98208 _43213 _43214 _43211 _43212).
Proof. exact (@lem3757063 (@IN (_98208 -> Prop) _43213 _43214) (term78 _98208 _43212 _43214) (term76 _98208 _43211 _43212)). Qed.
Lemma lem3757082 {_98208 : Type'} (_43211 : _98208 -> Prop) (_43213 : _98208 -> Prop) : (term49 _98208 _43211 _43213) = (term49 _98208 _43211 _43213).
Proof. exact (eq_refl (term49 _98208 _43211 _43213)). Qed.
Lemma lem3757083 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term40 _98208 _43213 _43214 _43211 _43212) = (term79 _98208 _43213 _43214 _43211 _43212).
Proof. exact (MK_COMB (@lem3757082 _98208 _43211 _43213) (@lem3757064 _98208 _43213 _43214 _43211 _43212)). Qed.
Lemma lem3757087 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3757088 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term79 _98208 _43213 _43214 _43211 _43212) = (term80 _98208 _43213 _43214 _43211 _43212).
Proof. exact (@lem3757087 (@IN (_98208 -> Prop) _43213 _43214) (term48 _98208 _43211 _43213) (term81 _98208 _43214 _43211 _43212)). Qed.
Lemma lem3757118 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term40 _98208 _43213 _43214 _43211 _43212) = (term80 _98208 _43213 _43214 _43211 _43212).
Proof. exact (TRANS (@lem3757083 _98208 _43213 _43214 _43211 _43212) (@lem3757088 _98208 _43213 _43214 _43211 _43212)). Qed.
Lemma lem3757119 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3757120 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term82 _98208 _43213 _43214 _43211 _43212) = (term83 _98208 _43213 _43214 _43211 _43212).
Proof. exact (MK_COMB (@lem3757119) (@lem3757118 _98208 _43213 _43214 _43211 _43212)). Qed.
Lemma lem3757150 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term80 _98208 _43213 _43214 _43211 _43212) = (term80 _98208 _43213 _43214 _43211 _43212).
Proof. exact (eq_refl (term80 _98208 _43213 _43214 _43211 _43212)). Qed.
Lemma lem3757151 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : ((term40 _98208 _43213 _43214 _43211 _43212) = (term80 _98208 _43213 _43214 _43211 _43212)) = ((term80 _98208 _43213 _43214 _43211 _43212) = (term80 _98208 _43213 _43214 _43211 _43212)).
Proof. exact (MK_COMB (@lem3757120 _98208 _43213 _43214 _43211 _43212) (@lem3757150 _98208 _43213 _43214 _43211 _43212)). Qed.
Lemma lem3757153 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3757154 (x : Prop) : (x = x) = True.
Proof. exact (@lem3757153 Prop x). Qed.
Lemma lem3757155 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : ((term80 _98208 _43213 _43214 _43211 _43212) = (term80 _98208 _43213 _43214 _43211 _43212)) = True.
Proof. exact (@lem3757154 (term80 _98208 _43213 _43214 _43211 _43212)). Qed.
Lemma lem3757156 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : ((term40 _98208 _43213 _43214 _43211 _43212) = (term80 _98208 _43213 _43214 _43211 _43212)) = True.
Proof. exact (TRANS (@lem3757151 _98208 _43213 _43214 _43211 _43212) (@lem3757155 _98208 _43213 _43214 _43211 _43212)). Qed.
Lemma lem3757157 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : True = ((term40 _98208 _43213 _43214 _43211 _43212) = (term80 _98208 _43213 _43214 _43211 _43212)).
Proof. exact (SYM (@lem3757156 _98208 _43213 _43214 _43211 _43212)). Qed.
Lemma lem3757158 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term40 _98208 _43213 _43214 _43211 _43212) = (term80 _98208 _43213 _43214 _43211 _43212).
Proof. exact (EQ_MP (@lem3757157 _98208 _43213 _43214 _43211 _43212) (@lem0)). Qed.
Lemma lem3757159 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : term80 _98208 _43213 _43214 _43211 _43212.
Proof. exact (EQ_MP (@lem3757158 _98208 _43213 _43214 _43211 _43212) (@lem3756869 _98208 _43213 _43214 _43211 _43212)). Qed.
Lemma lem3757161 (b : Prop) (a : Prop) : (a \/ b) = (term55 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3757162 {_98208 : Type'} (_43211 : _98208 -> Prop) (_43212 : type686 _98208) (_43213 : _98208 -> Prop) (_43214 : type686 _98208) : (term80 _98208 _43213 _43214 _43211 _43212) = (term84 _98208 _43211 _43212 _43213 _43214).
Proof. exact (@lem3757161 (term85 _98208 _43213 _43214 _43211 _43212) (@IN (_98208 -> Prop) _43213 _43214)). Qed.
Lemma lem3757164 (a : Prop) (b : Prop) : (term58 a b) = (term59 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3757165 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term86 _98208 _43213 _43214 _43211 _43212) = (term87 _98208 _43213 _43214 _43211 _43212).
Proof. exact (@lem3757164 (term48 _98208 _43211 _43213) (term81 _98208 _43214 _43211 _43212)). Qed.
Lemma lem3757167 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3757168 {_98208 : Type'} (_43211 : _98208 -> Prop) (_43213 : _98208 -> Prop) : (term62 _98208 _43211 _43213) = (_43211 = _43213).
Proof. exact (@lem3757167 (_43211 = _43213)). Qed.
Lemma lem3757169 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3757170 {_98208 : Type'} (_43211 : _98208 -> Prop) (_43213 : _98208 -> Prop) : (term63 _98208 _43211 _43213) = (term64 _98208 _43211 _43213).
Proof. exact (MK_COMB (@lem3757169) (@lem3757168 _98208 _43211 _43213)). Qed.
Lemma lem3757172 (a : Prop) (b : Prop) : (term58 a b) = (term59 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3757173 {_98208 : Type'} (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term88 _98208 _43214 _43211 _43212) = (term89 _98208 _43214 _43211 _43212).
Proof. exact (@lem3757172 (term78 _98208 _43212 _43214) (term76 _98208 _43211 _43212)). Qed.
Lemma lem3757175 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3757176 {_98208 : Type'} (_43212 : type686 _98208) (_43214 : type686 _98208) : (term90 _98208 _43212 _43214) = (_43212 = _43214).
Proof. exact (@lem3757175 (_43212 = _43214)). Qed.
Lemma lem3757177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3757178 {_98208 : Type'} (_43212 : type686 _98208) (_43214 : type686 _98208) : (term91 _98208 _43212 _43214) = (term92 _98208 _43212 _43214).
Proof. exact (MK_COMB (@lem3757177) (@lem3757176 _98208 _43212 _43214)). Qed.
Lemma lem3757180 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3757181 {_98208 : Type'} (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term93 _98208 _43211 _43212) = (@IN (_98208 -> Prop) _43211 _43212).
Proof. exact (@lem3757180 (@IN (_98208 -> Prop) _43211 _43212)). Qed.
Lemma lem3757182 {_98208 : Type'} (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term89 _98208 _43214 _43211 _43212) = (term94 _98208 _43214 _43211 _43212).
Proof. exact (MK_COMB (@lem3757178 _98208 _43212 _43214) (@lem3757181 _98208 _43211 _43212)). Qed.
Lemma lem3757183 {_98208 : Type'} (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term88 _98208 _43214 _43211 _43212) = (term94 _98208 _43214 _43211 _43212).
Proof. exact (TRANS (@lem3757173 _98208 _43214 _43211 _43212) (@lem3757182 _98208 _43214 _43211 _43212)). Qed.
Lemma lem3757184 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term87 _98208 _43213 _43214 _43211 _43212) = (term95 _98208 _43213 _43214 _43211 _43212).
Proof. exact (MK_COMB (@lem3757170 _98208 _43211 _43213) (@lem3757183 _98208 _43214 _43211 _43212)). Qed.
Lemma lem3757185 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term86 _98208 _43213 _43214 _43211 _43212) = (term95 _98208 _43213 _43214 _43211 _43212).
Proof. exact (TRANS (@lem3757165 _98208 _43213 _43214 _43211 _43212) (@lem3757184 _98208 _43213 _43214 _43211 _43212)). Qed.
Lemma lem3757186 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3757187 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) (_43211 : _98208 -> Prop) (_43212 : type686 _98208) : (term96 _98208 _43213 _43214 _43211 _43212) = (term97 _98208 _43213 _43214 _43211 _43212).
Proof. exact (MK_COMB (@lem3757186) (@lem3757185 _98208 _43213 _43214 _43211 _43212)). Qed.
Lemma lem3757188 {_98208 : Type'} (_43213 : _98208 -> Prop) (_43214 : type686 _98208) : (@IN (_98208 -> Prop) _43213 _43214) = (@IN (_98208 -> Prop) _43213 _43214).
Proof. exact (eq_refl (@IN (_98208 -> Prop) _43213 _43214)). Qed.
Lemma lem3757189 {_98208 : Type'} (_43211 : _98208 -> Prop) (_43212 : type686 _98208) (_43213 : _98208 -> Prop) (_43214 : type686 _98208) : (term84 _98208 _43211 _43212 _43213 _43214) = (term98 _98208 _43211 _43212 _43213 _43214).
Proof. exact (MK_COMB (@lem3757187 _98208 _43213 _43214 _43211 _43212) (@lem3757188 _98208 _43213 _43214)). Qed.
Lemma lem3757190 {_98208 : Type'} (_43211 : _98208 -> Prop) (_43212 : type686 _98208) (_43213 : _98208 -> Prop) (_43214 : type686 _98208) : (term80 _98208 _43213 _43214 _43211 _43212) = (term98 _98208 _43211 _43212 _43213 _43214).
Proof. exact (TRANS (@lem3757162 _98208 _43211 _43212 _43213 _43214) (@lem3757189 _98208 _43211 _43212 _43213 _43214)). Qed.
Lemma lem3757192 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) (h1 : @IN (_98208 -> Prop) t f) : term99 _98208 t f.
Proof. exact (conj (@lem3757038 _98208 f) (@lem3757045 _98208 t f h1)). Qed.
Lemma lem3757193 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : (@UNION _98208 s t) = t) (h2 : @IN (_98208 -> Prop) t f) : term100 _98208 s t f.
Proof. exact (conj (@lem3757029 _98208 s t h1) (@lem3757192 _98208 t f h2)). Qed.
Lemma lem3757195 {_98208 : Type'} (_43211 : _98208 -> Prop) (_43212 : type686 _98208) (_43213 : _98208 -> Prop) (_43214 : type686 _98208) : term98 _98208 _43211 _43212 _43213 _43214.
Proof. exact (EQ_MP (@lem3757190 _98208 _43211 _43212 _43213 _43214) (@lem3757159 _98208 _43213 _43214 _43211 _43212)). Qed.
Lemma lem3757196 {_98208 : Type'} (_43211 : _98208 -> Prop) (_43212 : type686 _98208) (_43213 : _98208 -> Prop) (_43214 : type686 _98208) : term98 _98208 _43211 _43212 _43213 _43214.
Proof. exact (@lem3757195 _98208 _43211 _43212 _43213 _43214). Qed.
Lemma lem3757197 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : term101 _98208 s t f.
Proof. exact (@lem3757196 _98208 t f (@UNION _98208 s t) f). Qed.
Lemma lem3757200 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : (@UNION _98208 s t) = t) (h2 : @IN (_98208 -> Prop) t f) : term26 _98208 s t f.
Proof. exact (@lem3757197 _98208 s t f (@lem3757193 _98208 s t f h1 h2)). Qed.
Lemma lem3757201 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : (@UNION _98208 s t) = t) (h2 : @IN (_98208 -> Prop) t f) : term102 _98208 s t f.
Proof. exact (fun h0 : term28 _98208 s t f => @lem3757200 _98208 s t f h1 h2). Qed.
Lemma lem3757203 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3757204 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : (term102 _98208 s t f) = (term26 _98208 s t f).
Proof. exact (@lem3757203 (term26 _98208 s t f)). Qed.
Lemma lem3757205 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : (@UNION _98208 s t) = t) (h2 : @IN (_98208 -> Prop) t f) : term26 _98208 s t f.
Proof. exact (EQ_MP (@lem3757204 _98208 s t f) (@lem3757201 _98208 s t f h1 h2)). Qed.
Lemma lem3757208 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3757210 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : (term28 _98208 s t f) = (term103 _98208 s t f).
Proof. exact (@lem3757208 (term26 _98208 s t f)). Qed.
Lemma lem3757213 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) : term103 _98208 s t f.
Proof. exact (EQ_MP (@lem3757210 _98208 s t f) (@lem3756787 _98208 s t f h1)). Qed.
Lemma lem3757216 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = t) (h3 : @IN (_98208 -> Prop) t f) : False.
Proof. exact (@lem3757213 _98208 s t f h1 (@lem3757205 _98208 s t f h2 h3)). Qed.
Lemma lem3757217 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = t) (h3 : @IN (_98208 -> Prop) t f) : term32.
Proof. exact (fun h0 : ~ False => @lem3757216 _98208 s t f h1 h2 h3). Qed.
Lemma lem3757219 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3757220 : term32 = False.
Proof. exact (@lem3757219 False). Qed.
Lemma lem3757221 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = t) (h3 : @IN (_98208 -> Prop) t f) : False.
Proof. exact (EQ_MP (@lem3757220) (@lem3757217 _98208 s t f h1 h2 h3)). Qed.
Lemma lem3757222 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = t) (h3 : @IN (_98208 -> Prop) t f) : ((@UNION _98208 s t) = t) = False.
Proof. exact (prop_ext (fun h4 : (@UNION _98208 s t) = t => @lem3757221 _98208 s t f h1 h2 h3) (fun h4 : False => @lem3756789 _98208 s t h2)). Qed.
Lemma lem3757223 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = t) (h3 : @IN (_98208 -> Prop) t f) : False.
Proof. exact (EQ_MP (@lem3757222 _98208 s t f h1 h2 h3) (@lem3756789 _98208 s t h2)). Qed.
Lemma lem3757224 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = t) (h3 : @IN (_98208 -> Prop) t f) : (@IN (_98208 -> Prop) t f) = False.
Proof. exact (prop_ext (fun h4 : @IN (_98208 -> Prop) t f => @lem3757223 _98208 s t f h1 h2 h3) (fun h4 : False => @lem3756783 _98208 t f h3)). Qed.
Lemma lem3757225 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = t) (h3 : @IN (_98208 -> Prop) t f) : False.
Proof. exact (EQ_MP (@lem3757224 _98208 s t f h1 h2 h3) (@lem3756783 _98208 t f h3)). Qed.
Lemma lem3757226 {_98208 : Type'} (f : type686 _98208) (t : _98208 -> Prop) (s : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = s) : ((@UNION _98208 s t) = s) = False.
Proof. exact (prop_ext (fun h3 : (@UNION _98208 s t) = s => @lem3756850 _98208 f t s h1 h2) (fun h3 : False => @lem3756781 _98208 t s h2)). Qed.
Lemma lem3757227 {_98208 : Type'} (f : type686 _98208) (t : _98208 -> Prop) (s : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = s) : False.
Proof. exact (EQ_MP (@lem3757226 _98208 f t s h1 h2) (@lem3756781 _98208 t s h2)). Qed.
Lemma lem3757228 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = t) (h3 : @IN (_98208 -> Prop) t f) : ((@UNION _98208 s t) = t) = False.
Proof. exact (prop_ext (fun h4 : (@UNION _98208 s t) = t => @lem3757225 _98208 s t f h1 h2 h3) (fun h4 : False => @lem3756773 _98208 s t h2)). Qed.
Lemma lem3757229 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = t) (h3 : @IN (_98208 -> Prop) t f) : False.
Proof. exact (EQ_MP (@lem3757228 _98208 s t f h1 h2 h3) (@lem3756773 _98208 s t h2)). Qed.
Lemma lem3757230 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = t) (h3 : @IN (_98208 -> Prop) t f) : (@IN (_98208 -> Prop) t f) = False.
Proof. exact (prop_ext (fun h4 : @IN (_98208 -> Prop) t f => @lem3757229 _98208 s t f h1 h2 h3) (fun h4 : False => @lem3756761 _98208 t f h3)). Qed.
Lemma lem3757231 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = t) (h3 : @IN (_98208 -> Prop) t f) : False.
Proof. exact (EQ_MP (@lem3757230 _98208 s t f h1 h2 h3) (@lem3756761 _98208 t f h3)). Qed.
Lemma lem3757232 {_98208 : Type'} (f : type686 _98208) (t : _98208 -> Prop) (s : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = s) : ((@UNION _98208 s t) = s) = False.
Proof. exact (prop_ext (fun h3 : (@UNION _98208 s t) = s => @lem3757227 _98208 f t s h1 h2) (fun h3 : False => @lem3756757 _98208 t s h2)). Qed.
Lemma lem3757233 {_98208 : Type'} (f : type686 _98208) (t : _98208 -> Prop) (s : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = s) : False.
Proof. exact (EQ_MP (@lem3757232 _98208 f t s h1 h2) (@lem3756757 _98208 t s h2)). Qed.
Lemma lem3757234 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = t) (h3 : @IN (_98208 -> Prop) t f) : ((@UNION _98208 s t) = t) = False.
Proof. exact (prop_ext (fun h4 : (@UNION _98208 s t) = t => @lem3757231 _98208 s t f h1 h2 h3) (fun h4 : False => @lem3756773 _98208 s t h2)). Qed.
Lemma lem3757235 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = t) (h3 : @IN (_98208 -> Prop) t f) : False.
Proof. exact (EQ_MP (@lem3757234 _98208 s t f h1 h2 h3) (@lem3756773 _98208 s t h2)). Qed.
Lemma lem3757236 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = t) (h3 : @IN (_98208 -> Prop) t f) : (@IN (_98208 -> Prop) t f) = False.
Proof. exact (prop_ext (fun h4 : @IN (_98208 -> Prop) t f => @lem3757235 _98208 s t f h1 h2 h3) (fun h4 : False => @lem3756761 _98208 t f h3)). Qed.
Lemma lem3757237 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = t) (h3 : @IN (_98208 -> Prop) t f) : False.
Proof. exact (EQ_MP (@lem3757236 _98208 s t f h1 h2 h3) (@lem3756761 _98208 t f h3)). Qed.
Lemma lem3757238 {_98208 : Type'} (f : type686 _98208) (t : _98208 -> Prop) (s : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = s) : ((@UNION _98208 s t) = s) = False.
Proof. exact (prop_ext (fun h3 : (@UNION _98208 s t) = s => @lem3757233 _98208 f t s h1 h2) (fun h3 : False => @lem3756757 _98208 t s h2)). Qed.
Lemma lem3757239 {_98208 : Type'} (f : type686 _98208) (t : _98208 -> Prop) (s : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : (@UNION _98208 s t) = s) : False.
Proof. exact (EQ_MP (@lem3757238 _98208 f t s h1 h2) (@lem3756757 _98208 t s h2)). Qed.
Lemma lem3757240 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : @IN (_98208 -> Prop) t f) (h3 : term24 _98208 s t) : False.
Proof. exact (or_elim (@lem3756705 _98208 s t h3) (fun h0 : (@UNION _98208 s t) = s => @lem3757239 _98208 f t s h1 h0) (fun h0 : (@UNION _98208 s t) = t => @lem3757237 _98208 s t f h1 h0 h2)). Qed.
Lemma lem3757241 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : @IN (_98208 -> Prop) t f) (h3 : term24 _98208 s t) : (@IN (_98208 -> Prop) t f) = False.
Proof. exact (prop_ext (fun h4 : @IN (_98208 -> Prop) t f => @lem3757240 _98208 f s t h1 h2 h3) (fun h4 : False => @lem3756711 _98208 t f h2)). Qed.
Lemma lem3757242 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : @IN (_98208 -> Prop) t f) (h3 : term24 _98208 s t) : False.
Proof. exact (EQ_MP (@lem3757241 _98208 f s t h1 h2 h3) (@lem3756711 _98208 t f h2)). Qed.
Lemma lem3757243 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : @IN (_98208 -> Prop) t f) (h3 : term24 _98208 s t) : (term24 _98208 s t) = False.
Proof. exact (prop_ext (fun h4 : term24 _98208 s t => @lem3757242 _98208 f s t h1 h2 h3) (fun h4 : False => @lem3756705 _98208 s t h3)). Qed.
Lemma lem3757244 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : @IN (_98208 -> Prop) t f) (h3 : term24 _98208 s t) : False.
Proof. exact (EQ_MP (@lem3757243 _98208 f s t h1 h2 h3) (@lem3756705 _98208 s t h3)). Qed.
Lemma lem3757245 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : @IN (_98208 -> Prop) t f) (h3 : term24 _98208 s t) : (@IN (_98208 -> Prop) t f) = False.
Proof. exact (prop_ext (fun h4 : @IN (_98208 -> Prop) t f => @lem3757244 _98208 f s t h1 h2 h3) (fun h4 : False => @lem3756671 _98208 t f h2)). Qed.
Lemma lem3757246 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : @IN (_98208 -> Prop) t f) (h3 : term24 _98208 s t) : False.
Proof. exact (EQ_MP (@lem3757245 _98208 f s t h1 h2 h3) (@lem3756671 _98208 t f h2)). Qed.
Lemma lem3757247 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : @IN (_98208 -> Prop) t f) (h3 : term24 _98208 s t) : (term24 _98208 s t) = False.
Proof. exact (prop_ext (fun h4 : term24 _98208 s t => @lem3757246 _98208 f s t h1 h2 h3) (fun h4 : False => @lem3756665 _98208 s t h3)). Qed.
Lemma lem3757248 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : @IN (_98208 -> Prop) t f) (h3 : term24 _98208 s t) : False.
Proof. exact (EQ_MP (@lem3757247 _98208 f s t h1 h2 h3) (@lem3756665 _98208 s t h3)). Qed.
Lemma lem3757249 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : @IN (_98208 -> Prop) t f) (h3 : term24 _98208 s t) : (term23 _98208 s t f) = False.
Proof. exact (prop_ext (fun h4 : term23 _98208 s t f => @lem3757248 _98208 f s t h1 h2 h3) (fun h4 : False => @lem3756655 _98208 s t f h1)). Qed.
Lemma lem3757250 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term23 _98208 s t f) (h2 : @IN (_98208 -> Prop) t f) (h3 : term24 _98208 s t) : False.
Proof. exact (EQ_MP (@lem3757249 _98208 f s t h1 h2 h3) (@lem3756655 _98208 s t f h1)). Qed.
Lemma lem3757251 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : @IN (_98208 -> Prop) t f) (h2 : term24 _98208 s t) : term22 _98208 s t f.
Proof. exact (fun h0 : term23 _98208 s t f => @lem3757250 _98208 f s t h0 h1 h2). Qed.
Lemma lem3757252 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : @IN (_98208 -> Prop) t f) (h2 : term24 _98208 s t) : term21 _98208 s t f.
Proof. exact (EQ_MP (@lem3756654 _98208 s t f) (@lem3757251 _98208 f s t h1 h2)). Qed.
Lemma lem3757253 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term24 _98208 s t) : term104 _98208 s t f.
Proof. exact (fun h0 : @IN (_98208 -> Prop) t f => @lem3757252 _98208 f s t h0 h1). Qed.
Lemma lem3757254 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : term1 _98208 s t f.
Proof. exact (fun h0 : term24 _98208 s t => @lem3757253 _98208 f s t h0). Qed.
Lemma lem3757259 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) : term12 _98208 t f.
Proof. exact (fun s : _98208 -> Prop => @lem3757254 _98208 s t f). Qed.
Lemma lem3757264 {_98208 : Type'} (f : type686 _98208) : term16 _98208 f.
Proof. exact (fun t : _98208 -> Prop => @lem3757259 _98208 t f). Qed.
Lemma lem3757269 {_98208 : Type'} : term20 _98208.
Proof. exact (fun f : type686 _98208 => @lem3757264 _98208 f). Qed.
Lemma lem3757270 {_98208 : Type'} : term19 _98208.
Proof. exact (EQ_MP (@lem3756648 _98208) (@lem3757269 _98208)). Qed.
Lemma lem3757271 {_98208 : Type'} (f : type686 _98208) : term105 _98208 f.
Proof. exact (@lem3757270 _98208 f). Qed.
Lemma lem3757272 {_98208 : Type'} (f : type686 _98208) : (term105 _98208 f) = (term15 _98208 f).
Proof. exact (eq_refl (term105 _98208 f)). Qed.
Lemma lem3757273 {_98208 : Type'} (f : type686 _98208) : term15 _98208 f.
Proof. exact (EQ_MP (@lem3757272 _98208 f) (@lem3757271 _98208 f)). Qed.
Lemma lem3757274 {_98208 : Type'} (f : type686 _98208) (t : _98208 -> Prop) : term106 _98208 f t.
Proof. exact (@lem3757273 _98208 f t). Qed.
Lemma lem3757275 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) : (term106 _98208 f t) = (term11 _98208 t f).
Proof. exact (eq_refl (term106 _98208 f t)). Qed.
Lemma lem3757276 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) : term11 _98208 t f.
Proof. exact (EQ_MP (@lem3757275 _98208 t f) (@lem3757274 _98208 f t)). Qed.
Lemma lem3757277 {_98208 : Type'} (t : _98208 -> Prop) (f : type686 _98208) (s : _98208 -> Prop) : term107 _98208 t f s.
Proof. exact (@lem3757276 _98208 t f s). Qed.
Lemma lem3757278 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : (term107 _98208 t f s) = (term2 _98208 s t f).
Proof. exact (eq_refl (term107 _98208 t f s)). Qed.
Lemma lem3757279 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : term2 _98208 s t f.
Proof. exact (EQ_MP (@lem3757278 _98208 s t f) (@lem3757277 _98208 t f s)). Qed.
Lemma lem3757281 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : term2 _98208 s t f.
Proof. exact (@lem3756540 _98208 s t f (@lem3757279 _98208 s t f)). Qed.
Lemma lem3757282 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term3 _98208 s t f) : False.
Proof. exact (@lem3757281 _98208 s t f (@lem3756524 _98208 s t f h1)). Qed.
Lemma lem3757283 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term3 _98208 s t f) : (term3 _98208 s t f) = False.
Proof. exact (prop_ext (fun h2 : term3 _98208 s t f => @lem3757282 _98208 s t f h1) (fun h2 : False => @lem3756524 _98208 s t f h1)). Qed.
Lemma lem3757284 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term3 _98208 s t f) : False.
Proof. exact (EQ_MP (@lem3757283 _98208 s t f h1) (@lem3756524 _98208 s t f h1)). Qed.
Lemma lem3757285 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : term2 _98208 s t f.
Proof. exact (fun h0 : term3 _98208 s t f => @lem3757284 _98208 s t f h0). Qed.
Lemma lem3757286 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : term1 _98208 s t f.
Proof. exact (EQ_MP (@lem3756523 _98208 s t f) (@lem3757285 _98208 s t f)). Qed.
Lemma lem3757287 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term1 _98208 s t f) : term1 _98208 s t f.
Proof. exact (h1). Qed.
Lemma lem3757288 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term24 _98208 s t) : term24 _98208 s t.
Proof. exact (h1). Qed.
Lemma lem3757289 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term1 _98208 s t f) (h2 : term24 _98208 s t) : term104 _98208 s t f.
Proof. exact (@lem3757287 _98208 s t f h1 (@lem3757288 _98208 s t h2)). Qed.
Lemma lem3757290 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term24 _98208 s t) : term108 _98208 s t f.
Proof. exact (fun h0 : term1 _98208 s t f => @lem3757289 _98208 f s t h0 h1). Qed.
Lemma lem3757291 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term1 _98208 s t f) : term1 _98208 s t f.
Proof. exact (h1). Qed.
Lemma lem3757292 {_98208 : Type'} (f : type686 _98208) (s : _98208 -> Prop) (t : _98208 -> Prop) (h1 : term1 _98208 s t f) (h2 : term24 _98208 s t) : term104 _98208 s t f.
Proof. exact (@lem3757290 _98208 f s t h2 (@lem3757291 _98208 s t f h1)). Qed.
Lemma lem3757293 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) (h1 : term1 _98208 s t f) : term1 _98208 s t f.
Proof. exact (fun h0 : term24 _98208 s t => @lem3757292 _98208 f s t h1 h0). Qed.
Lemma lem3757294 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : term109 _98208 s t f.
Proof. exact (fun h0 : term1 _98208 s t f => @lem3757293 _98208 s t f h0). Qed.
Lemma lem3757296 {A : Type'} (f : type686 A) : term110 A f.
Proof. exact (@lem9784 (f = (@EMPTY (A -> Prop)))). Qed.
Lemma lem3757297 {A : Type'} (f : type686 A) : (term110 A f) = (term111 A f).
Proof. exact (eq_refl (term110 A f)). Qed.
Lemma lem3757298 {A : Type'} (f : type686 A) : term111 A f.
Proof. exact (EQ_MP (@lem3757297 A f) (@lem3757296 A f)). Qed.
Lemma lem3757300 {A : Type'} (f : type686 A) (h1 : term112 A f) : term112 A f.
Proof. exact (h1). Qed.
Lemma lem3757315 (p : Prop) : term113 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem3757316 (p : Prop) : (term113 p) = (term114 p).
Proof. exact (eq_refl (term113 p)). Qed.
Lemma lem3757317 (p : Prop) : term114 p.
Proof. exact (EQ_MP (@lem3757316 p) (@lem3757315 p)). Qed.
Lemma lem3757318 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem3757319 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem3757334 (q : Prop) (r : Prop) : (term115 q r) = (term115 q r).
Proof. exact (eq_refl (term115 q r)). Qed.
Lemma lem3757335 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : (term116 q r p) = (term117 q r).
Proof. exact (MK_COMB (@lem3757334 q r) (@lem3757318 p h1)). Qed.
Lemma lem3757336 (q : Prop) (r : Prop) : (term117 q r) = ((term118 q r) = (term119 q r)).
Proof. exact (eq_refl (term117 q r)). Qed.
Lemma lem3757337 (q : Prop) (r : Prop) (p : Prop) : (term120 q r p) = (term120 q r p).
Proof. exact (eq_refl (term120 q r p)). Qed.
Lemma lem3757338 (p : Prop) (q : Prop) (r : Prop) : ((term116 q r p) = (term117 q r)) = ((term116 q r p) = ((term118 q r) = (term119 q r))).
Proof. exact (MK_COMB (@lem3757337 q r p) (@lem3757336 q r)). Qed.
Lemma lem3757339 (q : Prop) (p : Prop) (r : Prop) : (term116 q r p) = ((term121 p q r) = (term122 q p r)).
Proof. exact (eq_refl (term116 q r p)). Qed.
Lemma lem3757340 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3757341 (q : Prop) (p : Prop) (r : Prop) : (term120 q r p) = (term123 q p r).
Proof. exact (MK_COMB (@lem3757340) (@lem3757339 q p r)). Qed.
Lemma lem3757342 (q : Prop) (r : Prop) : ((term118 q r) = (term119 q r)) = ((term118 q r) = (term119 q r)).
Proof. exact (eq_refl ((term118 q r) = (term119 q r))). Qed.
Lemma lem3757343 (p : Prop) (q : Prop) (r : Prop) : ((term116 q r p) = ((term118 q r) = (term119 q r))) = (((term121 p q r) = (term122 q p r)) = ((term118 q r) = (term119 q r))).
Proof. exact (MK_COMB (@lem3757341 q p r) (@lem3757342 q r)). Qed.
Lemma lem3757344 (p : Prop) (q : Prop) (r : Prop) : ((term116 q r p) = (term117 q r)) = (((term121 p q r) = (term122 q p r)) = ((term118 q r) = (term119 q r))).
Proof. exact (TRANS (@lem3757338 p q r) (@lem3757343 p q r)). Qed.
Lemma lem3757345 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : ((term121 p q r) = (term122 q p r)) = ((term118 q r) = (term119 q r)).
Proof. exact (EQ_MP (@lem3757344 p q r) (@lem3757335 q r p h1)). Qed.
Lemma lem3757346 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : ((term118 q r) = (term119 q r)) = ((term121 p q r) = (term122 q p r)).
Proof. exact (SYM (@lem3757345 q r p h1)). Qed.
Lemma lem3757347 (q : Prop) (r : Prop) : (term115 q r) = (term115 q r).
Proof. exact (eq_refl (term115 q r)). Qed.
Lemma lem3757348 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : (term116 q r p) = (term124 q r).
Proof. exact (MK_COMB (@lem3757347 q r) (@lem3757319 p h1)). Qed.
Lemma lem3757349 (q : Prop) (r : Prop) : (term124 q r) = ((term125 q r) = (term126 q r)).
Proof. exact (eq_refl (term124 q r)). Qed.
Lemma lem3757350 (q : Prop) (r : Prop) (p : Prop) : (term120 q r p) = (term120 q r p).
Proof. exact (eq_refl (term120 q r p)). Qed.
Lemma lem3757351 (p : Prop) (q : Prop) (r : Prop) : ((term116 q r p) = (term124 q r)) = ((term116 q r p) = ((term125 q r) = (term126 q r))).
Proof. exact (MK_COMB (@lem3757350 q r p) (@lem3757349 q r)). Qed.
Lemma lem3757352 (q : Prop) (p : Prop) (r : Prop) : (term116 q r p) = ((term121 p q r) = (term122 q p r)).
Proof. exact (eq_refl (term116 q r p)). Qed.
Lemma lem3757353 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3757354 (q : Prop) (p : Prop) (r : Prop) : (term120 q r p) = (term123 q p r).
Proof. exact (MK_COMB (@lem3757353) (@lem3757352 q p r)). Qed.
Lemma lem3757355 (q : Prop) (r : Prop) : ((term125 q r) = (term126 q r)) = ((term125 q r) = (term126 q r)).
Proof. exact (eq_refl ((term125 q r) = (term126 q r))). Qed.
Lemma lem3757356 (p : Prop) (q : Prop) (r : Prop) : ((term116 q r p) = ((term125 q r) = (term126 q r))) = (((term121 p q r) = (term122 q p r)) = ((term125 q r) = (term126 q r))).
Proof. exact (MK_COMB (@lem3757354 q p r) (@lem3757355 q r)). Qed.
Lemma lem3757357 (p : Prop) (q : Prop) (r : Prop) : ((term116 q r p) = (term124 q r)) = (((term121 p q r) = (term122 q p r)) = ((term125 q r) = (term126 q r))).
Proof. exact (TRANS (@lem3757351 p q r) (@lem3757356 p q r)). Qed.
Lemma lem3757358 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : ((term121 p q r) = (term122 q p r)) = ((term125 q r) = (term126 q r)).
Proof. exact (EQ_MP (@lem3757357 p q r) (@lem3757348 q r p h1)). Qed.
Lemma lem3757359 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : ((term125 q r) = (term126 q r)) = ((term121 p q r) = (term122 q p r)).
Proof. exact (SYM (@lem3757358 q r p h1)). Qed.
Lemma lem3757363 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3757364 (q : Prop) (r : Prop) : (term118 q r) = (q /\ r).
Proof. exact (@lem3757363 (q /\ r)). Qed.
Lemma lem3757367 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3757368 (q : Prop) (r : Prop) : (term127 q r) = (term128 q r).
Proof. exact (MK_COMB (@lem3757367) (@lem3757364 q r)). Qed.
Lemma lem3757372 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3757373 (q : Prop) : (True -> q) = q.
Proof. exact (@lem3757372 q). Qed.
Lemma lem3757374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3757375 (q : Prop) : (term129 q) = (and q).
Proof. exact (MK_COMB (@lem3757374) (@lem3757373 q)). Qed.
Lemma lem3757377 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3757378 (r : Prop) : (True -> r) = r.
Proof. exact (@lem3757377 r). Qed.
Lemma lem3757379 (q : Prop) (r : Prop) : (term119 q r) = (q /\ r).
Proof. exact (MK_COMB (@lem3757375 q) (@lem3757378 r)). Qed.
Lemma lem3757382 (q : Prop) (r : Prop) : ((term118 q r) = (term119 q r)) = ((q /\ r) = (q /\ r)).
Proof. exact (MK_COMB (@lem3757368 q r) (@lem3757379 q r)). Qed.
Lemma lem3757384 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3757385 (x : Prop) : (x = x) = True.
Proof. exact (@lem3757384 Prop x). Qed.
Lemma lem3757386 (q : Prop) (r : Prop) : ((q /\ r) = (q /\ r)) = True.
Proof. exact (@lem3757385 (q /\ r)). Qed.
Lemma lem3757387 (q : Prop) (r : Prop) : ((term118 q r) = (term119 q r)) = True.
Proof. exact (TRANS (@lem3757382 q r) (@lem3757386 q r)). Qed.
Lemma lem3757388 (q : Prop) (r : Prop) : True = ((term118 q r) = (term119 q r)).
Proof. exact (SYM (@lem3757387 q r)). Qed.
Lemma lem3757389 (q : Prop) (r : Prop) : (term118 q r) = (term119 q r).
Proof. exact (EQ_MP (@lem3757388 q r) (@lem0)). Qed.
Lemma lem3757393 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3757394 (q : Prop) (r : Prop) : (term125 q r) = True.
Proof. exact (@lem3757393 (q /\ r)). Qed.
Lemma lem3757395 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3757396 (q : Prop) (r : Prop) : (term130 q r) = (@eq Prop True).
Proof. exact (MK_COMB (@lem3757395) (@lem3757394 q r)). Qed.
Lemma lem3757400 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3757401 (q : Prop) : (False -> q) = True.
Proof. exact (@lem3757400 q). Qed.
Lemma lem3757402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3757403 (q : Prop) : (term131 q) = (and True).
Proof. exact (MK_COMB (@lem3757402) (@lem3757401 q)). Qed.
Lemma lem3757405 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3757406 (r : Prop) : (False -> r) = True.
Proof. exact (@lem3757405 r). Qed.
Lemma lem3757407 (q : Prop) (r : Prop) : (term126 q r) = (True /\ True).
Proof. exact (MK_COMB (@lem3757403 q) (@lem3757406 r)). Qed.
Lemma lem3757409 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3757410 : (True /\ True) = True.
Proof. exact (@lem3757409 True). Qed.
Lemma lem3757411 (q : Prop) (r : Prop) : (term126 q r) = True.
Proof. exact (TRANS (@lem3757407 q r) (@lem3757410)). Qed.
Lemma lem3757412 (q : Prop) (r : Prop) : ((term125 q r) = (term126 q r)) = (True = True).
Proof. exact (MK_COMB (@lem3757396 q r) (@lem3757411 q r)). Qed.
Lemma lem3757414 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3757415 : (True = True) = True.
Proof. exact (@lem3757414 True). Qed.
Lemma lem3757416 (q : Prop) (r : Prop) : ((term125 q r) = (term126 q r)) = True.
Proof. exact (TRANS (@lem3757412 q r) (@lem3757415)). Qed.
Lemma lem3757417 (q : Prop) (r : Prop) : True = ((term125 q r) = (term126 q r)).
Proof. exact (SYM (@lem3757416 q r)). Qed.
Lemma lem3757418 (q : Prop) (r : Prop) : (term125 q r) = (term126 q r).
Proof. exact (EQ_MP (@lem3757417 q r) (@lem0)). Qed.
Lemma lem3757419 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : (term121 p q r) = (term122 q p r).
Proof. exact (EQ_MP (@lem3757359 q r p h1) (@lem3757418 q r)). Qed.
Lemma lem3757420 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : (term121 p q r) = (term122 q p r).
Proof. exact (EQ_MP (@lem3757346 q r p h1) (@lem3757389 q r)). Qed.
Lemma lem3757424 {A : Type'} (x : A) : term132 A x.
Proof. exact (@lem3278799 A x). Qed.
Lemma lem3757425 {A : Type'} (x : A) : (term132 A x) = (term133 A x).
Proof. exact (eq_refl (term132 A x)). Qed.
Lemma lem3757426 {A : Type'} (x : A) : term133 A x.
Proof. exact (EQ_MP (@lem3757425 A x) (@lem3757424 A x)). Qed.
Lemma lem3757427 {A : Type'} (x : A) (s : A -> Prop) : term134 A x s.
Proof. exact (@lem3757426 A x s). Qed.
Lemma lem3757428 {A : Type'} (x : A) (s : A -> Prop) : (term134 A x s) = (term135 A x s).
Proof. exact (eq_refl (term134 A x s)). Qed.
Lemma lem3757429 {A : Type'} (x : A) (s : A -> Prop) : term135 A x s.
Proof. exact (EQ_MP (@lem3757428 A x s) (@lem3757427 A x s)). Qed.
Lemma lem3757430 {A : Type'} (x : A) (s : A -> Prop) : term136 A x s.
Proof. exact (@lem82 ((@INSERT A x s) = (@EMPTY A))). Qed.
Lemma lem3757443 {A : Type'} (P : A -> Prop) : term137 A P.
Proof. exact (@lem4997 A P). Qed.
Lemma lem3757444 {A : Type'} (P : A -> Prop) : (term137 A P) = (term138 A P).
Proof. exact (eq_refl (term137 A P)). Qed.
Lemma lem3757445 {A : Type'} (P : A -> Prop) : term138 A P.
Proof. exact (EQ_MP (@lem3757444 A P) (@lem3757443 A P)). Qed.
Lemma lem3757446 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term139 A P Q.
Proof. exact (@lem3757445 A P Q). Qed.
Lemma lem3757447 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term139 A P Q) = ((term140 A P Q) = (term141 A P Q)).
Proof. exact (eq_refl (term139 A P Q)). Qed.
Lemma lem3757449 {_83983 : Type'} (P : _83983 -> Prop) : term142 _83983 P.
Proof. exact (@lem3207453 _83983 P). Qed.
Lemma lem3757450 {_83983 : Type'} (P : _83983 -> Prop) : (term142 _83983 P) = (term143 _83983 P).
Proof. exact (eq_refl (term142 _83983 P)). Qed.
Lemma lem3757451 {_83983 : Type'} (P : _83983 -> Prop) : term143 _83983 P.
Proof. exact (EQ_MP (@lem3757450 _83983 P) (@lem3757449 _83983 P)). Qed.
Lemma lem3757452 {_83983 : Type'} (P : _83983 -> Prop) (a : _83983) : term144 _83983 P a.
Proof. exact (@lem3757451 _83983 P a). Qed.
Lemma lem3757453 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : (term144 _83983 P a) = (term145 _83983 a P).
Proof. exact (eq_refl (term144 _83983 P a)). Qed.
Lemma lem3757454 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) : term145 _83983 a P.
Proof. exact (EQ_MP (@lem3757453 _83983 a P) (@lem3757452 _83983 P a)). Qed.
Lemma lem3757455 {_83983 : Type'} (a : _83983) (P : _83983 -> Prop) (s : _83983 -> Prop) : term146 _83983 a P s.
Proof. exact (@lem3757454 _83983 a P s). Qed.
Lemma lem3757456 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term146 _83983 a P s) = ((term147 _83983 a s P) = (term148 _83983 a s P)).
Proof. exact (eq_refl (term146 _83983 a P s)). Qed.
Lemma lem3757458 {A : Type'} (P : Prop) : term149 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem3757459 {A : Type'} (P : Prop) : (term149 A P) = (term150 A P).
Proof. exact (eq_refl (term149 A P)). Qed.
Lemma lem3757460 {A : Type'} (P : Prop) : term150 A P.
Proof. exact (EQ_MP (@lem3757459 A P) (@lem3757458 A P)). Qed.
Lemma lem3757461 {A : Type'} (P : Prop) (Q : A -> Prop) : term151 A P Q.
Proof. exact (@lem3757460 A P Q). Qed.
Lemma lem3757462 {A : Type'} (P : Prop) (Q : A -> Prop) : (term151 A P Q) = ((term152 A P Q) = (term153 A P Q)).
Proof. exact (eq_refl (term151 A P Q)). Qed.
Lemma lem3757464 {A : Type'} (h1 : term154 A) : term154 A.
Proof. exact (h1). Qed.
Lemma lem3757465 {A : Type'} (FINITE' : type686 A) (h1 : term154 A) : term155 A FINITE'.
Proof. exact (@lem3757464 A h1 FINITE'). Qed.
Lemma lem3757466 {A : Type'} (FINITE' : type686 A) : (term155 A FINITE') = (term156 A FINITE').
Proof. exact (eq_refl (term155 A FINITE')). Qed.
Lemma lem3757467 {A : Type'} (FINITE' : type686 A) (h1 : term154 A) : term156 A FINITE'.
Proof. exact (EQ_MP (@lem3757466 A FINITE') (@lem3757465 A FINITE' h1)). Qed.
Lemma lem3757468 {A : Type'} (FINITE' : type686 A) (h1 : term157 A FINITE') : term157 A FINITE'.
Proof. exact (h1). Qed.
Lemma lem3757469 {A : Type'} (FINITE' : type686 A) (h1 : term154 A) (h2 : term157 A FINITE') : term158 A FINITE'.
Proof. exact (@lem3757467 A FINITE' h1 (@lem3757468 A FINITE' h2)). Qed.
Lemma lem3757470 {A : Type'} (FINITE' : type686 A) (h1 : term157 A FINITE') : term159 A FINITE'.
Proof. exact (fun h0 : term154 A => @lem3757469 A FINITE' h0 h1). Qed.
Lemma lem3757471 {A : Type'} (h1 : term154 A) : term154 A.
Proof. exact (h1). Qed.
Lemma lem3757472 {A : Type'} (FINITE' : type686 A) (h1 : term154 A) (h2 : term157 A FINITE') : term158 A FINITE'.
Proof. exact (@lem3757470 A FINITE' h2 (@lem3757471 A h1)). Qed.
Lemma lem3757473 {A : Type'} (FINITE' : type686 A) (h1 : term154 A) : term156 A FINITE'.
Proof. exact (fun h0 : term157 A FINITE' => @lem3757472 A FINITE' h1 h0). Qed.
Lemma lem3757474 {A : Type'} (h1 : term154 A) : term154 A.
Proof. exact (fun FINITE' : type686 A => @lem3757473 A FINITE' h1). Qed.
Lemma lem3757475 {A : Type'} : term160 A.
Proof. exact (fun h0 : term154 A => @lem3757474 A h0). Qed.
Lemma lem3757476 {A : Type'} : term154 A.
Proof. exact (@lem3757475 A (@lem3197567 A)). Qed.
Lemma lem3757477 {A : Type'} (FINITE' : type686 A) : term155 A FINITE'.
Proof. exact (@lem3757476 A FINITE'). Qed.
Lemma lem3757478 {A : Type'} (FINITE' : type686 A) : (term155 A FINITE') = (term156 A FINITE').
Proof. exact (eq_refl (term155 A FINITE')). Qed.
Lemma lem3757485 (p : Prop) (q : Prop) (r : Prop) : (term161 p q r) = (term162 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem3757486 {A : Type'} (f : type686 A) : (term163 A f) = (term164 A f).
Proof. exact (@lem3757485 (@FINITE (A -> Prop) f) (term165 A f) (term166 A f)). Qed.
Lemma lem3757490 (p : Prop) (q : Prop) (r : Prop) : (term161 p q r) = (term162 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem3757491 {A : Type'} (f : type686 A) : (term167 A f) = (term168 A f).
Proof. exact (@lem3757490 (term112 A f) (term169 A f) (term166 A f)). Qed.
Lemma lem3757507 (p : Prop) (q : Prop) (r : Prop) : (term161 p q r) = (term162 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem3757508 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term170 A f t s) = (term171 A f t s).
Proof. exact (@lem3757507 (@IN (A -> Prop) s f) (@IN (A -> Prop) t f) (term172 A t s)). Qed.
Lemma lem3757515 {A : Type'} (f : type686 A) (s : A -> Prop) : (term173 A f s) = (term174 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3757508 A f t s)). Qed.
Lemma lem3757516 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3757517 {A : Type'} (f : type686 A) (s : A -> Prop) : (term175 A f s) = (term176 A f s).
Proof. exact (MK_COMB (@lem3757516 A) (@lem3757515 A f s)). Qed.
Lemma lem3757522 {A : Type'} (f : type686 A) : (term177 A f) = (term178 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3757517 A f s)). Qed.
Lemma lem3757523 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3757524 {A : Type'} (f : type686 A) : (term169 A f) = (term179 A f).
Proof. exact (MK_COMB (@lem3757523 A) (@lem3757522 A f)). Qed.
Lemma lem3757529 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3757530 {A : Type'} (f : type686 A) : (term180 A f) = (term181 A f).
Proof. exact (MK_COMB (@lem3757529) (@lem3757524 A f)). Qed.
Lemma lem3757531 {A : Type'} (f : type686 A) : (term166 A f) = (term166 A f).
Proof. exact (eq_refl (term166 A f)). Qed.
Lemma lem3757532 {A : Type'} (f : type686 A) : (term182 A f) = (term183 A f).
Proof. exact (MK_COMB (@lem3757530 A f) (@lem3757531 A f)). Qed.
Lemma lem3757535 {A : Type'} (f : type686 A) : (term184 A f) = (term184 A f).
Proof. exact (eq_refl (term184 A f)). Qed.
Lemma lem3757536 {A : Type'} (f : type686 A) : (term168 A f) = (term185 A f).
Proof. exact (MK_COMB (@lem3757535 A f) (@lem3757532 A f)). Qed.
Lemma lem3757539 {A : Type'} (f : type686 A) : (term167 A f) = (term185 A f).
Proof. exact (TRANS (@lem3757491 A f) (@lem3757536 A f)). Qed.
Lemma lem3757540 {A : Type'} (f : type686 A) : (term186 A f) = (term186 A f).
Proof. exact (eq_refl (term186 A f)). Qed.
Lemma lem3757541 {A : Type'} (f : type686 A) : (term164 A f) = (term187 A f).
Proof. exact (MK_COMB (@lem3757540 A f) (@lem3757539 A f)). Qed.
Lemma lem3757544 {A : Type'} (f : type686 A) : (term163 A f) = (term187 A f).
Proof. exact (TRANS (@lem3757486 A f) (@lem3757541 A f)). Qed.
Lemma lem3757545 {A : Type'} : (term188 A) = (term189 A).
Proof. exact (fun_ext (fun f : type686 A => @lem3757544 A f)). Qed.
Lemma lem3757546 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3757547 {A : Type'} : (term190 A) = (term191 A).
Proof. exact (MK_COMB (@lem3757546 A) (@lem3757545 A)). Qed.
Lemma lem3757552 {A : Type'} : (term191 A) = (term190 A).
Proof. exact (SYM (@lem3757547 A)). Qed.
Lemma lem3757554 {A : Type'} (FINITE' : type686 A) : term156 A FINITE'.
Proof. exact (EQ_MP (@lem3757478 A FINITE') (@lem3757477 A FINITE')). Qed.
Lemma lem3757555 {A : Type'} (FINITE' : type180 A) : term192 A FINITE'.
Proof. exact (@lem3757554 (A -> Prop) FINITE'). Qed.
Lemma lem3757556 {A : Type'} : term193 A.
Proof. exact (@lem3757555 A (term194 A)). Qed.
Lemma lem3757557 {A : Type'} : (term195 A) = (term196 A).
Proof. exact (eq_refl (term195 A)). Qed.
Lemma lem3757558 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3757559 {A : Type'} : (term197 A) = (term198 A).
Proof. exact (MK_COMB (@lem3757558) (@lem3757557 A)). Qed.
Lemma lem3757560 {A : Type'} (s : type686 A) : (term199 A s) = (term185 A s).
Proof. exact (eq_refl (term199 A s)). Qed.
Lemma lem3757561 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3757562 {A : Type'} (s : type686 A) : (term200 A s) = (term201 A s).
Proof. exact (MK_COMB (@lem3757561) (@lem3757560 A s)). Qed.
Lemma lem3757563 {A : Type'} (x : A -> Prop) (s : type686 A) : (term202 A x s) = (term203 A x s).
Proof. exact (eq_refl (term202 A x s)). Qed.
Lemma lem3757564 {A : Type'} (x : A -> Prop) (s : type686 A) : (term204 A x s) = (term205 A x s).
Proof. exact (MK_COMB (@lem3757562 A s) (@lem3757563 A x s)). Qed.
Lemma lem3757565 {A : Type'} (x : A -> Prop) : (term206 A x) = (term207 A x).
Proof. exact (fun_ext (fun s : type686 A => @lem3757564 A x s)). Qed.
Lemma lem3757566 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3757567 {A : Type'} (x : A -> Prop) : (term208 A x) = (term209 A x).
Proof. exact (MK_COMB (@lem3757566 A) (@lem3757565 A x)). Qed.
Lemma lem3757568 {A : Type'} : (term210 A) = (term211 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3757567 A x)). Qed.
Lemma lem3757569 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3757570 {A : Type'} : (term212 A) = (term213 A).
Proof. exact (MK_COMB (@lem3757569 A) (@lem3757568 A)). Qed.
Lemma lem3757571 {A : Type'} : (term214 A) = (term215 A).
Proof. exact (MK_COMB (@lem3757559 A) (@lem3757570 A)). Qed.
Lemma lem3757572 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3757573 {A : Type'} : (term216 A) = (term217 A).
Proof. exact (MK_COMB (@lem3757572) (@lem3757571 A)). Qed.
Lemma lem3757574 {A : Type'} (f : type686 A) : (term199 A f) = (term185 A f).
Proof. exact (eq_refl (term199 A f)). Qed.
Lemma lem3757575 {A : Type'} (f : type686 A) : (term186 A f) = (term186 A f).
Proof. exact (eq_refl (term186 A f)). Qed.
Lemma lem3757576 {A : Type'} (f : type686 A) : (term218 A f) = (term187 A f).
Proof. exact (MK_COMB (@lem3757575 A f) (@lem3757574 A f)). Qed.
Lemma lem3757577 {A : Type'} : (term219 A) = (term189 A).
Proof. exact (fun_ext (fun f : type686 A => @lem3757576 A f)). Qed.
Lemma lem3757578 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3757579 {A : Type'} : (term220 A) = (term191 A).
Proof. exact (MK_COMB (@lem3757578 A) (@lem3757577 A)). Qed.
Lemma lem3757580 {A : Type'} : (term193 A) = (term221 A).
Proof. exact (MK_COMB (@lem3757573 A) (@lem3757579 A)). Qed.
Lemma lem3757581 {A : Type'} : term221 A.
Proof. exact (EQ_MP (@lem3757580 A) (@lem3757556 A)). Qed.
Lemma lem3757587 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3757588 {A : Type'} (x : type686 A) : (x = x) = True.
Proof. exact (@lem3757587 (type686 A) x). Qed.
Lemma lem3757589 {A : Type'} : ((@EMPTY (A -> Prop)) = (@EMPTY (A -> Prop))) = True.
Proof. exact (@lem3757588 A (@EMPTY (A -> Prop))). Qed.
Lemma lem3757590 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3757591 {A : Type'} : (term222 A) = (~ True).
Proof. exact (MK_COMB (@lem3757590) (@lem3757589 A)). Qed.
Lemma lem3757593 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3757594 {A : Type'} : (term222 A) = False.
Proof. exact (TRANS (@lem3757591 A) (@lem3757593)). Qed.
Lemma lem3757595 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3757596 {A : Type'} : (term223 A) = (imp False).
Proof. exact (MK_COMB (@lem3757595) (@lem3757594 A)). Qed.
Lemma lem3757604 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem3757462 A P Q) (@lem3757461 A P Q)). Qed.
Lemma lem3757605 {A : Type'} (P : Prop) (Q : type686 A) : (term224 A P Q) = (term225 A P Q).
Proof. exact (@lem3757604 (A -> Prop) P Q). Qed.
Lemma lem3757606 {A : Type'} (s : A -> Prop) : (term226 A s) = (term227 A s).
Proof. exact (@lem3757605 A (@IN (A -> Prop) s (@EMPTY (A -> Prop))) (term228 A s)). Qed.
Lemma lem3757607 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term229 A s t) = (term230 A t s).
Proof. exact (eq_refl (term229 A s t)). Qed.
Lemma lem3757608 {A : Type'} (s : A -> Prop) : (term231 A s) = (term231 A s).
Proof. exact (eq_refl (term231 A s)). Qed.
Lemma lem3757609 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term232 A s t) = (term233 A t s).
Proof. exact (MK_COMB (@lem3757608 A s) (@lem3757607 A t s)). Qed.
Lemma lem3757610 {A : Type'} (s : A -> Prop) : (term234 A s) = (term235 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3757609 A t s)). Qed.
Lemma lem3757611 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3757612 {A : Type'} (s : A -> Prop) : (term226 A s) = (term236 A s).
Proof. exact (MK_COMB (@lem3757611 A) (@lem3757610 A s)). Qed.
Lemma lem3757613 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3757614 {A : Type'} (s : A -> Prop) : (term237 A s) = (term238 A s).
Proof. exact (MK_COMB (@lem3757613) (@lem3757612 A s)). Qed.
Lemma lem3757615 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term229 A s t) = (term230 A t s).
Proof. exact (eq_refl (term229 A s t)). Qed.
Lemma lem3757616 {A : Type'} (s : A -> Prop) : (term239 A s) = (term228 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3757615 A t s)). Qed.
Lemma lem3757617 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3757618 {A : Type'} (s : A -> Prop) : (term240 A s) = (term241 A s).
Proof. exact (MK_COMB (@lem3757617 A) (@lem3757616 A s)). Qed.
Lemma lem3757619 {A : Type'} (s : A -> Prop) : (term231 A s) = (term231 A s).
Proof. exact (eq_refl (term231 A s)). Qed.
Lemma lem3757620 {A : Type'} (s : A -> Prop) : (term227 A s) = (term242 A s).
Proof. exact (MK_COMB (@lem3757619 A s) (@lem3757618 A s)). Qed.
Lemma lem3757621 {A : Type'} (s : A -> Prop) : ((term226 A s) = (term227 A s)) = ((term236 A s) = (term242 A s)).
Proof. exact (MK_COMB (@lem3757614 A s) (@lem3757620 A s)). Qed.
Lemma lem3757622 {A : Type'} (s : A -> Prop) : (term236 A s) = (term242 A s).
Proof. exact (EQ_MP (@lem3757621 A s) (@lem3757606 A s)). Qed.
Lemma lem3757653 {A : Type'} : (term243 A) = (term244 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3757622 A s)). Qed.
Lemma lem3757654 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3757655 {A : Type'} : (term245 A) = (term246 A).
Proof. exact (MK_COMB (@lem3757654 A) (@lem3757653 A)). Qed.
Lemma lem3757680 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3757681 {A : Type'} : (term247 A) = (term248 A).
Proof. exact (MK_COMB (@lem3757680) (@lem3757655 A)). Qed.
Lemma lem3757682 {A : Type'} : (term249 A) = (term249 A).
Proof. exact (eq_refl (term249 A)). Qed.
Lemma lem3757683 {A : Type'} : (term250 A) = (term251 A).
Proof. exact (MK_COMB (@lem3757681 A) (@lem3757682 A)). Qed.
Lemma lem3757686 {A : Type'} : (term196 A) = (term252 A).
Proof. exact (MK_COMB (@lem3757596 A) (@lem3757683 A)). Qed.
Lemma lem3757688 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3757689 {A : Type'} : (term252 A) = True.
Proof. exact (@lem3757688 (term251 A)). Qed.
Lemma lem3757690 {A : Type'} : (term196 A) = True.
Proof. exact (TRANS (@lem3757686 A) (@lem3757689 A)). Qed.
Lemma lem3757691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3757692 {A : Type'} : (term198 A) = (and True).
Proof. exact (MK_COMB (@lem3757691) (@lem3757690 A)). Qed.
Lemma lem3757734 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem3757462 A P Q) (@lem3757461 A P Q)). Qed.
Lemma lem3757735 {A : Type'} (P : Prop) (Q : type686 A) : (term224 A P Q) = (term225 A P Q).
Proof. exact (@lem3757734 (A -> Prop) P Q). Qed.
Lemma lem3757736 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term253 A s s') = (term254 A s s').
Proof. exact (@lem3757735 A (@IN (A -> Prop) s' s) (term255 A s s')). Qed.
Lemma lem3757737 {A : Type'} (s : type686 A) (t : A -> Prop) (s' : A -> Prop) : (term256 A s s' t) = (term257 A s t s').
Proof. exact (eq_refl (term256 A s s' t)). Qed.
Lemma lem3757738 {A : Type'} (s : A -> Prop) (s' : type686 A) : (term258 A s s') = (term258 A s s').
Proof. exact (eq_refl (term258 A s s')). Qed.
Lemma lem3757739 {A : Type'} (s : type686 A) (t : A -> Prop) (s' : A -> Prop) : (term259 A s s' t) = (term171 A s t s').
Proof. exact (MK_COMB (@lem3757738 A s' s) (@lem3757737 A s t s')). Qed.
Lemma lem3757740 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term260 A s s') = (term174 A s s').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3757739 A s t s')). Qed.
Lemma lem3757741 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3757742 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term253 A s s') = (term176 A s s').
Proof. exact (MK_COMB (@lem3757741 A) (@lem3757740 A s s')). Qed.
Lemma lem3757743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3757744 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term261 A s s') = (term262 A s s').
Proof. exact (MK_COMB (@lem3757743) (@lem3757742 A s s')). Qed.
Lemma lem3757745 {A : Type'} (s : type686 A) (t : A -> Prop) (s' : A -> Prop) : (term256 A s s' t) = (term257 A s t s').
Proof. exact (eq_refl (term256 A s s' t)). Qed.
Lemma lem3757746 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term263 A s s') = (term255 A s s').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3757745 A s t s')). Qed.
Lemma lem3757747 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3757748 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term264 A s s') = (term265 A s s').
Proof. exact (MK_COMB (@lem3757747 A) (@lem3757746 A s s')). Qed.
Lemma lem3757749 {A : Type'} (s : A -> Prop) (s' : type686 A) : (term258 A s s') = (term258 A s s').
Proof. exact (eq_refl (term258 A s s')). Qed.
Lemma lem3757750 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term254 A s s') = (term266 A s s').
Proof. exact (MK_COMB (@lem3757749 A s' s) (@lem3757748 A s s')). Qed.
Lemma lem3757751 {A : Type'} (s : type686 A) (s' : A -> Prop) : ((term253 A s s') = (term254 A s s')) = ((term176 A s s') = (term266 A s s')).
Proof. exact (MK_COMB (@lem3757744 A s s') (@lem3757750 A s s')). Qed.
Lemma lem3757752 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term176 A s s') = (term266 A s s').
Proof. exact (EQ_MP (@lem3757751 A s s') (@lem3757736 A s s')). Qed.
Lemma lem3757783 {A : Type'} (s : type686 A) : (term178 A s) = (term267 A s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3757752 A s s')). Qed.
Lemma lem3757784 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3757785 {A : Type'} (s : type686 A) : (term179 A s) = (term268 A s).
Proof. exact (MK_COMB (@lem3757784 A) (@lem3757783 A s)). Qed.
Lemma lem3757810 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3757811 {A : Type'} (s : type686 A) : (term181 A s) = (term269 A s).
Proof. exact (MK_COMB (@lem3757810) (@lem3757785 A s)). Qed.
Lemma lem3757812 {A : Type'} (s : type686 A) : (term166 A s) = (term166 A s).
Proof. exact (eq_refl (term166 A s)). Qed.
Lemma lem3757813 {A : Type'} (s : type686 A) : (term183 A s) = (term270 A s).
Proof. exact (MK_COMB (@lem3757811 A s) (@lem3757812 A s)). Qed.
Lemma lem3757816 {A : Type'} (s : type686 A) : (term184 A s) = (term184 A s).
Proof. exact (eq_refl (term184 A s)). Qed.
Lemma lem3757817 {A : Type'} (s : type686 A) : (term185 A s) = (term271 A s).
Proof. exact (MK_COMB (@lem3757816 A s) (@lem3757813 A s)). Qed.
Lemma lem3757820 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3757821 {A : Type'} (s : type686 A) : (term201 A s) = (term272 A s).
Proof. exact (MK_COMB (@lem3757820) (@lem3757817 A s)). Qed.
Lemma lem3757835 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem3757462 A P Q) (@lem3757461 A P Q)). Qed.
Lemma lem3757836 {A : Type'} (P : Prop) (Q : type686 A) : (term224 A P Q) = (term225 A P Q).
Proof. exact (@lem3757835 (A -> Prop) P Q). Qed.
Lemma lem3757837 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term273 A x s s') = (term274 A x s s').
Proof. exact (@lem3757836 A (term275 A s' x s) (term276 A x s s')). Qed.
Lemma lem3757838 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) (s' : A -> Prop) : (term277 A x s s' t) = (term278 A x s t s').
Proof. exact (eq_refl (term277 A x s s' t)). Qed.
Lemma lem3757839 {A : Type'} (s : A -> Prop) (x : A -> Prop) (s' : type686 A) : (term279 A s x s') = (term279 A s x s').
Proof. exact (eq_refl (term279 A s x s')). Qed.
Lemma lem3757840 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) (s' : A -> Prop) : (term280 A x s s' t) = (term281 A x s t s').
Proof. exact (MK_COMB (@lem3757839 A s' x s) (@lem3757838 A x s t s')). Qed.
Lemma lem3757841 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term282 A x s s') = (term283 A x s s').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3757840 A x s t s')). Qed.
Lemma lem3757842 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3757843 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term273 A x s s') = (term284 A x s s').
Proof. exact (MK_COMB (@lem3757842 A) (@lem3757841 A x s s')). Qed.
Lemma lem3757844 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3757845 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term285 A x s s') = (term286 A x s s').
Proof. exact (MK_COMB (@lem3757844) (@lem3757843 A x s s')). Qed.
Lemma lem3757846 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) (s' : A -> Prop) : (term277 A x s s' t) = (term278 A x s t s').
Proof. exact (eq_refl (term277 A x s s' t)). Qed.
Lemma lem3757847 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term287 A x s s') = (term276 A x s s').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3757846 A x s t s')). Qed.
Lemma lem3757848 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3757849 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term288 A x s s') = (term289 A x s s').
Proof. exact (MK_COMB (@lem3757848 A) (@lem3757847 A x s s')). Qed.
Lemma lem3757850 {A : Type'} (s : A -> Prop) (x : A -> Prop) (s' : type686 A) : (term279 A s x s') = (term279 A s x s').
Proof. exact (eq_refl (term279 A s x s')). Qed.
Lemma lem3757851 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term274 A x s s') = (term290 A x s s').
Proof. exact (MK_COMB (@lem3757850 A s' x s) (@lem3757849 A x s s')). Qed.
Lemma lem3757852 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : ((term273 A x s s') = (term274 A x s s')) = ((term284 A x s s') = (term290 A x s s')).
Proof. exact (MK_COMB (@lem3757845 A x s s') (@lem3757851 A x s s')). Qed.
Lemma lem3757853 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term284 A x s s') = (term290 A x s s').
Proof. exact (EQ_MP (@lem3757852 A x s s') (@lem3757837 A x s s')). Qed.
Lemma lem3757857 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term147 _83983 a s P) = (term148 _83983 a s P).
Proof. exact (EQ_MP (@lem3757456 _83983 a s P) (@lem3757455 _83983 a P s)). Qed.
Lemma lem3757858 {A : Type'} (a : A -> Prop) (s : type686 A) (P : type686 A) : (term291 A a s P) = (term292 A a s P).
Proof. exact (@lem3757857 (A -> Prop) a s P). Qed.
Lemma lem3757859 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term293 A x s s') = (term294 A x s s').
Proof. exact (@lem3757858 A x s (term295 A s')). Qed.
Lemma lem3757860 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term296 A s t) = (term172 A t s).
Proof. exact (eq_refl (term296 A s t)). Qed.
Lemma lem3757861 {A : Type'} (t : A -> Prop) (x : A -> Prop) (s : type686 A) : (term279 A t x s) = (term279 A t x s).
Proof. exact (eq_refl (term279 A t x s)). Qed.
Lemma lem3757862 {A : Type'} (x : A -> Prop) (s : type686 A) (t : A -> Prop) (s' : A -> Prop) : (term297 A x s s' t) = (term278 A x s t s').
Proof. exact (MK_COMB (@lem3757861 A t x s) (@lem3757860 A t s')). Qed.
Lemma lem3757863 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term298 A x s s') = (term276 A x s s').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3757862 A x s t s')). Qed.
Lemma lem3757864 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3757865 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term293 A x s s') = (term289 A x s s').
Proof. exact (MK_COMB (@lem3757864 A) (@lem3757863 A x s s')). Qed.
Lemma lem3757866 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3757867 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term299 A x s s') = (term300 A x s s').
Proof. exact (MK_COMB (@lem3757866) (@lem3757865 A x s s')). Qed.
Lemma lem3757868 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term296 A s x) = (term172 A x s).
Proof. exact (eq_refl (term296 A s x)). Qed.
Lemma lem3757869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3757870 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term301 A s x) = (term302 A x s).
Proof. exact (MK_COMB (@lem3757869) (@lem3757868 A x s)). Qed.
Lemma lem3757871 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term296 A s t) = (term172 A t s).
Proof. exact (eq_refl (term296 A s t)). Qed.
Lemma lem3757872 {A : Type'} (t : A -> Prop) (s : type686 A) : (term258 A t s) = (term258 A t s).
Proof. exact (eq_refl (term258 A t s)). Qed.
Lemma lem3757873 {A : Type'} (s : type686 A) (t : A -> Prop) (s' : A -> Prop) : (term303 A s s' t) = (term257 A s t s').
Proof. exact (MK_COMB (@lem3757872 A t s) (@lem3757871 A t s')). Qed.
Lemma lem3757874 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term304 A s s') = (term255 A s s').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3757873 A s t s')). Qed.
Lemma lem3757875 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3757876 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term305 A s s') = (term265 A s s').
Proof. exact (MK_COMB (@lem3757875 A) (@lem3757874 A s s')). Qed.
Lemma lem3757877 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term294 A x s s') = (term306 A x s s').
Proof. exact (MK_COMB (@lem3757870 A x s') (@lem3757876 A s s')). Qed.
Lemma lem3757878 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : ((term293 A x s s') = (term294 A x s s')) = ((term289 A x s s') = (term306 A x s s')).
Proof. exact (MK_COMB (@lem3757867 A x s s') (@lem3757877 A x s s')). Qed.
Lemma lem3757879 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term289 A x s s') = (term306 A x s s').
Proof. exact (EQ_MP (@lem3757878 A x s s') (@lem3757859 A x s s')). Qed.
Lemma lem3757912 {A : Type'} (s : A -> Prop) (x : A -> Prop) (s' : type686 A) : (term279 A s x s') = (term279 A s x s').
Proof. exact (eq_refl (term279 A s x s')). Qed.
Lemma lem3757913 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term290 A x s s') = (term307 A x s s').
Proof. exact (MK_COMB (@lem3757912 A s' x s) (@lem3757879 A x s s')). Qed.
Lemma lem3757916 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term284 A x s s') = (term307 A x s s').
Proof. exact (TRANS (@lem3757853 A x s s') (@lem3757913 A x s s')). Qed.
Lemma lem3757917 {A : Type'} (x : A -> Prop) (s : type686 A) : (term308 A x s) = (term309 A x s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3757916 A x s s')). Qed.
Lemma lem3757918 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3757919 {A : Type'} (x : A -> Prop) (s : type686 A) : (term310 A x s) = (term311 A x s).
Proof. exact (MK_COMB (@lem3757918 A) (@lem3757917 A x s)). Qed.
Lemma lem3757921 {_83983 : Type'} (a : _83983) (s : _83983 -> Prop) (P : _83983 -> Prop) : (term147 _83983 a s P) = (term148 _83983 a s P).
Proof. exact (EQ_MP (@lem3757456 _83983 a s P) (@lem3757455 _83983 a P s)). Qed.
Lemma lem3757922 {A : Type'} (a : A -> Prop) (s : type686 A) (P : type686 A) : (term291 A a s P) = (term292 A a s P).
Proof. exact (@lem3757921 (A -> Prop) a s P). Qed.
Lemma lem3757923 {A : Type'} (x : A -> Prop) (s : type686 A) : (term312 A x s) = (term313 A x s).
Proof. exact (@lem3757922 A x s (term314 A x s)). Qed.
Lemma lem3757924 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term315 A x s s') = (term306 A x s s').
Proof. exact (eq_refl (term315 A x s s')). Qed.
Lemma lem3757925 {A : Type'} (s : A -> Prop) (x : A -> Prop) (s' : type686 A) : (term279 A s x s') = (term279 A s x s').
Proof. exact (eq_refl (term279 A s x s')). Qed.
Lemma lem3757926 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term316 A x s s') = (term307 A x s s').
Proof. exact (MK_COMB (@lem3757925 A s' x s) (@lem3757924 A x s s')). Qed.
Lemma lem3757927 {A : Type'} (x : A -> Prop) (s : type686 A) : (term317 A x s) = (term309 A x s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3757926 A x s s')). Qed.
Lemma lem3757928 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3757929 {A : Type'} (x : A -> Prop) (s : type686 A) : (term312 A x s) = (term311 A x s).
Proof. exact (MK_COMB (@lem3757928 A) (@lem3757927 A x s)). Qed.
Lemma lem3757930 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3757931 {A : Type'} (x : A -> Prop) (s : type686 A) : (term318 A x s) = (term319 A x s).
Proof. exact (MK_COMB (@lem3757930) (@lem3757929 A x s)). Qed.
Lemma lem3757932 {A : Type'} (s : type686 A) (x : A -> Prop) : (term320 A s x) = (term321 A s x).
Proof. exact (eq_refl (term320 A s x)). Qed.
Lemma lem3757933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3757934 {A : Type'} (s : type686 A) (x : A -> Prop) : (term322 A s x) = (term323 A s x).
Proof. exact (MK_COMB (@lem3757933) (@lem3757932 A s x)). Qed.
Lemma lem3757935 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term315 A x s s') = (term306 A x s s').
Proof. exact (eq_refl (term315 A x s s')). Qed.
Lemma lem3757936 {A : Type'} (s : A -> Prop) (s' : type686 A) : (term258 A s s') = (term258 A s s').
Proof. exact (eq_refl (term258 A s s')). Qed.
Lemma lem3757937 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term324 A x s s') = (term325 A x s s').
Proof. exact (MK_COMB (@lem3757936 A s' s) (@lem3757935 A x s s')). Qed.
Lemma lem3757938 {A : Type'} (x : A -> Prop) (s : type686 A) : (term326 A x s) = (term327 A x s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3757937 A x s s')). Qed.
Lemma lem3757939 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3757940 {A : Type'} (x : A -> Prop) (s : type686 A) : (term328 A x s) = (term329 A x s).
Proof. exact (MK_COMB (@lem3757939 A) (@lem3757938 A x s)). Qed.
Lemma lem3757941 {A : Type'} (x : A -> Prop) (s : type686 A) : (term313 A x s) = (term330 A x s).
Proof. exact (MK_COMB (@lem3757934 A s x) (@lem3757940 A x s)). Qed.
Lemma lem3757942 {A : Type'} (x : A -> Prop) (s : type686 A) : ((term312 A x s) = (term313 A x s)) = ((term311 A x s) = (term330 A x s)).
Proof. exact (MK_COMB (@lem3757931 A x s) (@lem3757941 A x s)). Qed.
Lemma lem3757943 {A : Type'} (x : A -> Prop) (s : type686 A) : (term311 A x s) = (term330 A x s).
Proof. exact (EQ_MP (@lem3757942 A x s) (@lem3757923 A x s)). Qed.
Lemma lem3757949 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem1834 t)). Qed.
Lemma lem3757950 {A : Type'} (x : A -> Prop) : (term331 A x) = (@SUBSET A x x).
Proof. exact (@lem3757949 (@SUBSET A x x)). Qed.
Lemma lem3757951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3757952 {A : Type'} (x : A -> Prop) : (term332 A x) = (term333 A x).
Proof. exact (MK_COMB (@lem3757951) (@lem3757950 A x)). Qed.
Lemma lem3757981 {A : Type'} (s : type686 A) (x : A -> Prop) : (term265 A s x) = (term265 A s x).
Proof. exact (eq_refl (term265 A s x)). Qed.
Lemma lem3757982 {A : Type'} (s : type686 A) (x : A -> Prop) : (term321 A s x) = (term334 A s x).
Proof. exact (MK_COMB (@lem3757952 A x) (@lem3757981 A s x)). Qed.
Lemma lem3757985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3757986 {A : Type'} (s : type686 A) (x : A -> Prop) : (term323 A s x) = (term335 A s x).
Proof. exact (MK_COMB (@lem3757985) (@lem3757982 A s x)). Qed.
Lemma lem3758045 {A : Type'} (x : A -> Prop) (s : type686 A) : (term329 A x s) = (term329 A x s).
Proof. exact (eq_refl (term329 A x s)). Qed.
Lemma lem3758046 {A : Type'} (x : A -> Prop) (s : type686 A) : (term330 A x s) = (term336 A x s).
Proof. exact (MK_COMB (@lem3757986 A s x) (@lem3758045 A x s)). Qed.
Lemma lem3758049 {A : Type'} (x : A -> Prop) (s : type686 A) : (term311 A x s) = (term336 A x s).
Proof. exact (TRANS (@lem3757943 A x s) (@lem3758046 A x s)). Qed.
Lemma lem3758050 {A : Type'} (x : A -> Prop) (s : type686 A) : (term310 A x s) = (term336 A x s).
Proof. exact (TRANS (@lem3757919 A x s) (@lem3758049 A x s)). Qed.
Lemma lem3758051 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3758052 {A : Type'} (x : A -> Prop) (s : type686 A) : (term337 A x s) = (term338 A x s).
Proof. exact (MK_COMB (@lem3758051) (@lem3758050 A x s)). Qed.
Lemma lem3758054 {_86841 : Type'} (s : _86841 -> Prop) (u : type686 _86841) : (term339 _86841 s u) = (term340 _86841 s u).
Proof. exact (EQ_MP (@lem3324017 _86841 s u) (@lem3325374 _86841 s u)). Qed.
Lemma lem3758055 {A : Type'} (s : A -> Prop) (u : type686 A) : (term339 A s u) = (term340 A s u).
Proof. exact (@lem3758054 A s u). Qed.
Lemma lem3758056 {A : Type'} (x : A -> Prop) (s : type686 A) : (term339 A x s) = (term340 A x s).
Proof. exact (@lem3758055 A x s). Qed.
Lemma lem3758057 {A : Type'} : (@IN (A -> Prop)) = (@IN (A -> Prop)).
Proof. exact (eq_refl (@IN (A -> Prop))). Qed.
Lemma lem3758058 {A : Type'} (x : A -> Prop) (s : type686 A) : (term341 A x s) = (term342 A x s).
Proof. exact (MK_COMB (@lem3758057 A) (@lem3758056 A x s)). Qed.
Lemma lem3758059 {A : Type'} (x : A -> Prop) (s : type686 A) : (@INSERT (A -> Prop) x s) = (@INSERT (A -> Prop) x s).
Proof. exact (eq_refl (@INSERT (A -> Prop) x s)). Qed.
Lemma lem3758060 {A : Type'} (x : A -> Prop) (s : type686 A) : (term343 A x s) = (term344 A x s).
Proof. exact (MK_COMB (@lem3758058 A x s) (@lem3758059 A x s)). Qed.
Lemma lem3758061 {A : Type'} (x : A -> Prop) (s : type686 A) : (term345 A x s) = (term346 A x s).
Proof. exact (MK_COMB (@lem3758052 A x s) (@lem3758060 A x s)). Qed.
Lemma lem3758064 {A : Type'} (x : A -> Prop) (s : type686 A) : (term347 A x s) = (term347 A x s).
Proof. exact (eq_refl (term347 A x s)). Qed.
Lemma lem3758065 {A : Type'} (x : A -> Prop) (s : type686 A) : (term203 A x s) = (term348 A x s).
Proof. exact (MK_COMB (@lem3758064 A x s) (@lem3758061 A x s)). Qed.
Lemma lem3758068 {A : Type'} (x : A -> Prop) (s : type686 A) : (term205 A x s) = (term349 A x s).
Proof. exact (MK_COMB (@lem3757821 A s) (@lem3758065 A x s)). Qed.
Lemma lem3758071 {A : Type'} (x : A -> Prop) : (term207 A x) = (term350 A x).
Proof. exact (fun_ext (fun s : type686 A => @lem3758068 A x s)). Qed.
Lemma lem3758072 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3758073 {A : Type'} (x : A -> Prop) : (term209 A x) = (term351 A x).
Proof. exact (MK_COMB (@lem3758072 A) (@lem3758071 A x)). Qed.
Lemma lem3758098 {A : Type'} : (term211 A) = (term352 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3758073 A x)). Qed.
Lemma lem3758099 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3758100 {A : Type'} : (term213 A) = (term353 A).
Proof. exact (MK_COMB (@lem3758099 A) (@lem3758098 A)). Qed.
Lemma lem3758105 {A : Type'} : (term215 A) = (term354 A).
Proof. exact (MK_COMB (@lem3757692 A) (@lem3758100 A)). Qed.
Lemma lem3758107 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3758108 {A : Type'} : (term354 A) = (term353 A).
Proof. exact (@lem3758107 (term353 A)). Qed.
Lemma lem3758295 {A : Type'} : (term215 A) = (term353 A).
Proof. exact (TRANS (@lem3758105 A) (@lem3758108 A)). Qed.
Lemma lem3758296 {A : Type'} : (term353 A) = (term215 A).
Proof. exact (SYM (@lem3758295 A)). Qed.
Lemma lem3758330 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = False.
Proof. exact (@lem3757430 A x s (@lem3757429 A x s)). Qed.
Lemma lem3758331 {A : Type'} (x : A -> Prop) (s : type686 A) : ((@INSERT (A -> Prop) x s) = (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3758330 (A -> Prop) x s). Qed.
Lemma lem3758332 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3758333 {A : Type'} (x : A -> Prop) (s : type686 A) : (term355 A x s) = (~ False).
Proof. exact (MK_COMB (@lem3758332) (@lem3758331 A x s)). Qed.
Lemma lem3758335 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3758336 {A : Type'} (x : A -> Prop) (s : type686 A) : (term355 A x s) = True.
Proof. exact (TRANS (@lem3758333 A x s) (@lem3758335)). Qed.
Lemma lem3758337 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3758338 {A : Type'} (x : A -> Prop) (s : type686 A) : (term347 A x s) = (imp True).
Proof. exact (MK_COMB (@lem3758337) (@lem3758336 A x s)). Qed.
Lemma lem3758358 (q : Prop) (p : Prop) (r : Prop) : (term121 p q r) = (term122 q p r).
Proof. exact (or_elim (@lem3757317 p) (fun h0 : p = True => @lem3757420 q r p h0) (fun h0 : p = False => @lem3757419 q r p h0)). Qed.
Lemma lem3758359 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term325 A x s s') = (term356 A x s s').
Proof. exact (@lem3758358 (term172 A x s') (@IN (A -> Prop) s' s) (term265 A s s')). Qed.
Lemma lem3758376 {A : Type'} (x : A -> Prop) (s : type686 A) : (term327 A x s) = (term357 A x s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3758359 A x s s')). Qed.
Lemma lem3758377 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3758378 {A : Type'} (x : A -> Prop) (s : type686 A) : (term329 A x s) = (term358 A x s).
Proof. exact (MK_COMB (@lem3758377 A) (@lem3758376 A x s)). Qed.
Lemma lem3758380 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem3757447 A P Q) (@lem3757446 A P Q)). Qed.
Lemma lem3758381 {A : Type'} (P : type686 A) (Q : type686 A) : (term359 A P Q) = (term360 A P Q).
Proof. exact (@lem3758380 (A -> Prop) P Q). Qed.
Lemma lem3758382 {A : Type'} (x : A -> Prop) (s : type686 A) : (term361 A x s) = (term362 A x s).
Proof. exact (@lem3758381 A (term363 A s x) (term267 A s)). Qed.
Lemma lem3758383 {A : Type'} (s : type686 A) (x : A -> Prop) (s' : A -> Prop) : (term364 A s x s') = (term365 A s x s').
Proof. exact (eq_refl (term364 A s x s')). Qed.
Lemma lem3758384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3758385 {A : Type'} (s : type686 A) (x : A -> Prop) (s' : A -> Prop) : (term366 A s x s') = (term367 A s x s').
Proof. exact (MK_COMB (@lem3758384) (@lem3758383 A s x s')). Qed.
Lemma lem3758386 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term368 A s s') = (term266 A s s').
Proof. exact (eq_refl (term368 A s s')). Qed.
Lemma lem3758387 {A : Type'} (x : A -> Prop) (s : type686 A) (s' : A -> Prop) : (term369 A x s s') = (term356 A x s s').
Proof. exact (MK_COMB (@lem3758385 A s x s') (@lem3758386 A s s')). Qed.
Lemma lem3758388 {A : Type'} (x : A -> Prop) (s : type686 A) : (term370 A x s) = (term357 A x s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3758387 A x s s')). Qed.
Lemma lem3758389 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3758390 {A : Type'} (x : A -> Prop) (s : type686 A) : (term361 A x s) = (term358 A x s).
Proof. exact (MK_COMB (@lem3758389 A) (@lem3758388 A x s)). Qed.
Lemma lem3758391 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3758392 {A : Type'} (x : A -> Prop) (s : type686 A) : (term371 A x s) = (term372 A x s).
Proof. exact (MK_COMB (@lem3758391) (@lem3758390 A x s)). Qed.
Lemma lem3758393 {A : Type'} (s : type686 A) (x : A -> Prop) (s' : A -> Prop) : (term364 A s x s') = (term365 A s x s').
Proof. exact (eq_refl (term364 A s x s')). Qed.
Lemma lem3758394 {A : Type'} (s : type686 A) (x : A -> Prop) : (term373 A s x) = (term363 A s x).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3758393 A s x s')). Qed.
Lemma lem3758395 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3758396 {A : Type'} (s : type686 A) (x : A -> Prop) : (term374 A s x) = (term375 A s x).
Proof. exact (MK_COMB (@lem3758395 A) (@lem3758394 A s x)). Qed.
Lemma lem3758397 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3758398 {A : Type'} (s : type686 A) (x : A -> Prop) : (term376 A s x) = (term377 A s x).
Proof. exact (MK_COMB (@lem3758397) (@lem3758396 A s x)). Qed.
Lemma lem3758399 {A : Type'} (s : type686 A) (s' : A -> Prop) : (term368 A s s') = (term266 A s s').
Proof. exact (eq_refl (term368 A s s')). Qed.
Lemma lem3758400 {A : Type'} (s : type686 A) : (term378 A s) = (term267 A s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3758399 A s s')). Qed.
Lemma lem3758401 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3758402 {A : Type'} (s : type686 A) : (term379 A s) = (term268 A s).
Proof. exact (MK_COMB (@lem3758401 A) (@lem3758400 A s)). Qed.
Lemma lem3758403 {A : Type'} (x : A -> Prop) (s : type686 A) : (term362 A x s) = (term380 A x s).
Proof. exact (MK_COMB (@lem3758398 A s x) (@lem3758402 A s)). Qed.
Lemma lem3758404 {A : Type'} (x : A -> Prop) (s : type686 A) : ((term361 A x s) = (term362 A x s)) = ((term358 A x s) = (term380 A x s)).
Proof. exact (MK_COMB (@lem3758392 A x s) (@lem3758403 A x s)). Qed.
Lemma lem3758405 {A : Type'} (x : A -> Prop) (s : type686 A) : (term358 A x s) = (term380 A x s).
Proof. exact (EQ_MP (@lem3758404 A x s) (@lem3758382 A x s)). Qed.
Lemma lem3758430 {A : Type'} (x : A -> Prop) (s : type686 A) : (term329 A x s) = (term380 A x s).
Proof. exact (TRANS (@lem3758378 A x s) (@lem3758405 A x s)). Qed.
Lemma lem3758431 {A : Type'} (s : type686 A) (x : A -> Prop) : (term335 A s x) = (term335 A s x).
Proof. exact (eq_refl (term335 A s x)). Qed.
Lemma lem3758432 {A : Type'} (x : A -> Prop) (s : type686 A) : (term336 A x s) = (term381 A x s).
Proof. exact (MK_COMB (@lem3758431 A s x) (@lem3758430 A x s)). Qed.
Lemma lem3758435 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3758436 {A : Type'} (x : A -> Prop) (s : type686 A) : (term338 A x s) = (term382 A x s).
Proof. exact (MK_COMB (@lem3758435) (@lem3758432 A x s)). Qed.
Lemma lem3758437 {A : Type'} (x : A -> Prop) (s : type686 A) : (term344 A x s) = (term344 A x s).
Proof. exact (eq_refl (term344 A x s)). Qed.
Lemma lem3758438 {A : Type'} (x : A -> Prop) (s : type686 A) : (term346 A x s) = (term383 A x s).
Proof. exact (MK_COMB (@lem3758436 A x s) (@lem3758437 A x s)). Qed.
Lemma lem3758441 {A : Type'} (x : A -> Prop) (s : type686 A) : (term348 A x s) = (term384 A x s).
Proof. exact (MK_COMB (@lem3758338 A x s) (@lem3758438 A x s)). Qed.
Lemma lem3758443 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3758444 {A : Type'} (x : A -> Prop) (s : type686 A) : (term384 A x s) = (term383 A x s).
Proof. exact (@lem3758443 (term383 A x s)). Qed.
Lemma lem3758483 {A : Type'} (x : A -> Prop) (s : type686 A) : (term348 A x s) = (term383 A x s).
Proof. exact (TRANS (@lem3758441 A x s) (@lem3758444 A x s)). Qed.
Lemma lem3758484 {A : Type'} (s : type686 A) : (term272 A s) = (term272 A s).
Proof. exact (eq_refl (term272 A s)). Qed.
Lemma lem3758485 {A : Type'} (x : A -> Prop) (s : type686 A) : (term349 A x s) = (term385 A x s).
Proof. exact (MK_COMB (@lem3758484 A s) (@lem3758483 A x s)). Qed.
Lemma lem3758488 {A : Type'} (x : A -> Prop) : (term350 A x) = (term386 A x).
Proof. exact (fun_ext (fun s : type686 A => @lem3758485 A x s)). Qed.
Lemma lem3758489 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3758490 {A : Type'} (x : A -> Prop) : (term351 A x) = (term387 A x).
Proof. exact (MK_COMB (@lem3758489 A) (@lem3758488 A x)). Qed.
Lemma lem3758495 {A : Type'} : (term352 A) = (term388 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3758490 A x)). Qed.
Lemma lem3758496 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3758497 {A : Type'} : (term353 A) = (term389 A).
Proof. exact (MK_COMB (@lem3758496 A) (@lem3758495 A)). Qed.
Lemma lem3758502 {A : Type'} : (term389 A) = (term353 A).
Proof. exact (SYM (@lem3758497 A)). Qed.
Lemma lem3758503 {A : Type'} : term390 A.
Proof. exact (proj2 (@lem3235853 A)). Qed.
Lemma lem3758504 {A : Type'} (s : A -> Prop) : term391 A s.
Proof. exact (@lem3758503 A s). Qed.
Lemma lem3758505 {A : Type'} (s : A -> Prop) : (term391 A s) = ((@UNION A s (@EMPTY A)) = s).
Proof. exact (eq_refl (term391 A s)). Qed.
Lemma lem3758511 {A : Type'} (x : A) : term392 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3758512 {A : Type'} (x : A) : (term392 A x) = (term393 A x).
Proof. exact (eq_refl (term392 A x)). Qed.
Lemma lem3758513 {A : Type'} (x : A) : term393 A x.
Proof. exact (EQ_MP (@lem3758512 A x) (@lem3758511 A x)). Qed.
Lemma lem3758514 {A : Type'} (x : A) (y : A) : term394 A x y.
Proof. exact (@lem3758513 A x y). Qed.
Lemma lem3758515 {A : Type'} (y : A) (x : A) : (term394 A x y) = (term395 A y x).
Proof. exact (eq_refl (term394 A x y)). Qed.
Lemma lem3758516 {A : Type'} (y : A) (x : A) : term395 A y x.
Proof. exact (EQ_MP (@lem3758515 A y x) (@lem3758514 A x y)). Qed.
Lemma lem3758517 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term396 A y x s.
Proof. exact (@lem3758516 A y x s). Qed.
Lemma lem3758518 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term396 A y x s) = ((term397 A x y s) = (term398 A y x s)).
Proof. exact (eq_refl (term396 A y x s)). Qed.
Lemma lem3758527 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3758528 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem3758529 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@eq ((A -> Prop) -> Prop) f) = (@eq ((A -> Prop) -> Prop) (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3758528 A) (@lem3758527 A f h1)). Qed.
Lemma lem3758530 {A : Type'} : (@EMPTY (A -> Prop)) = (@EMPTY (A -> Prop)).
Proof. exact (eq_refl (@EMPTY (A -> Prop))). Qed.
Lemma lem3758531 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (f = (@EMPTY (A -> Prop))) = ((@EMPTY (A -> Prop)) = (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3758529 A f h1) (@lem3758530 A)). Qed.
Lemma lem3758533 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3758534 {A : Type'} (x : type686 A) : (x = x) = True.
Proof. exact (@lem3758533 (type686 A) x). Qed.
Lemma lem3758535 {A : Type'} : ((@EMPTY (A -> Prop)) = (@EMPTY (A -> Prop))) = True.
Proof. exact (@lem3758534 A (@EMPTY (A -> Prop))). Qed.
Lemma lem3758536 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (f = (@EMPTY (A -> Prop))) = True.
Proof. exact (TRANS (@lem3758531 A f h1) (@lem3758535 A)). Qed.
Lemma lem3758537 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3758538 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term112 A f) = (~ True).
Proof. exact (MK_COMB (@lem3758537) (@lem3758536 A f h1)). Qed.
Lemma lem3758540 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3758541 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term112 A f) = False.
Proof. exact (TRANS (@lem3758538 A f h1) (@lem3758540)). Qed.
Lemma lem3758542 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3758543 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term184 A f) = (imp False).
Proof. exact (MK_COMB (@lem3758542) (@lem3758541 A f h1)). Qed.
Lemma lem3758553 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3758554 {A : Type'} (s : A -> Prop) : (@IN (A -> Prop) s) = (@IN (A -> Prop) s).
Proof. exact (eq_refl (@IN (A -> Prop) s)). Qed.
Lemma lem3758555 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@IN (A -> Prop) s f) = (@IN (A -> Prop) s (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3758554 A s) (@lem3758553 A f h1)). Qed.
Lemma lem3758556 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3758557 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term258 A s f) = (term231 A s).
Proof. exact (MK_COMB (@lem3758556) (@lem3758555 A s f h1)). Qed.
Lemma lem3758565 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3758566 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t) = (@IN (A -> Prop) t).
Proof. exact (eq_refl (@IN (A -> Prop) t)). Qed.
Lemma lem3758567 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@IN (A -> Prop) t f) = (@IN (A -> Prop) t (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3758566 A t) (@lem3758565 A f h1)). Qed.
Lemma lem3758568 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3758569 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term258 A t f) = (term231 A t).
Proof. exact (MK_COMB (@lem3758568) (@lem3758567 A t f h1)). Qed.
Lemma lem3758572 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term172 A t s) = (term172 A t s).
Proof. exact (eq_refl (term172 A t s)). Qed.
Lemma lem3758573 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term257 A f t s) = (term230 A t s).
Proof. exact (MK_COMB (@lem3758569 A t f h1) (@lem3758572 A t s)). Qed.
Lemma lem3758576 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term255 A f s) = (term228 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3758573 A t s f h1)). Qed.
Lemma lem3758577 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3758578 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term265 A f s) = (term241 A s).
Proof. exact (MK_COMB (@lem3758577 A) (@lem3758576 A s f h1)). Qed.
Lemma lem3758583 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term266 A f s) = (term242 A s).
Proof. exact (MK_COMB (@lem3758557 A s f h1) (@lem3758578 A s f h1)). Qed.
Lemma lem3758586 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term267 A f) = (term244 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3758583 A s f h1)). Qed.
Lemma lem3758587 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3758588 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term268 A f) = (term246 A).
Proof. exact (MK_COMB (@lem3758587 A) (@lem3758586 A f h1)). Qed.
Lemma lem3758593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3758594 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term269 A f) = (term248 A).
Proof. exact (MK_COMB (@lem3758593) (@lem3758588 A f h1)). Qed.
Lemma lem3758596 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3758597 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem3758598 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@UNIONS A f) = (@UNIONS A (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3758597 A) (@lem3758596 A f h1)). Qed.
Lemma lem3758600 {_86801 : Type'} : (@UNIONS _86801 (@EMPTY (_86801 -> Prop))) = (@EMPTY _86801).
Proof. exact (EQ_MP (@lem3322101 _86801) (@lem3322164 _86801)). Qed.
Lemma lem3758601 {A : Type'} : (@UNIONS A (@EMPTY (A -> Prop))) = (@EMPTY A).
Proof. exact (@lem3758600 A). Qed.
Lemma lem3758602 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@UNIONS A f) = (@EMPTY A).
Proof. exact (TRANS (@lem3758598 A f h1) (@lem3758601 A)). Qed.
Lemma lem3758603 {A : Type'} : (@IN (A -> Prop)) = (@IN (A -> Prop)).
Proof. exact (eq_refl (@IN (A -> Prop))). Qed.
Lemma lem3758604 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term399 A f) = (@IN (A -> Prop) (@EMPTY A)).
Proof. exact (MK_COMB (@lem3758603 A) (@lem3758602 A f h1)). Qed.
Lemma lem3758606 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3758607 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term166 A f) = (@IN (A -> Prop) (@EMPTY A) (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3758604 A f h1) (@lem3758606 A f h1)). Qed.
Lemma lem3758608 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term270 A f) = (term400 A).
Proof. exact (MK_COMB (@lem3758594 A f h1) (@lem3758607 A f h1)). Qed.
Lemma lem3758611 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term271 A f) = (term401 A).
Proof. exact (MK_COMB (@lem3758543 A f h1) (@lem3758608 A f h1)). Qed.
Lemma lem3758613 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3758614 {A : Type'} : (term401 A) = True.
Proof. exact (@lem3758613 (term400 A)). Qed.
Lemma lem3758615 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term271 A f) = True.
Proof. exact (TRANS (@lem3758611 A f h1) (@lem3758614 A)). Qed.
Lemma lem3758616 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3758617 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term272 A f) = (imp True).
Proof. exact (MK_COMB (@lem3758616) (@lem3758615 A f h1)). Qed.
Lemma lem3758631 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3758632 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t) = (@IN (A -> Prop) t).
Proof. exact (eq_refl (@IN (A -> Prop) t)). Qed.
Lemma lem3758633 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@IN (A -> Prop) t f) = (@IN (A -> Prop) t (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3758632 A t) (@lem3758631 A f h1)). Qed.
Lemma lem3758634 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3758635 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term258 A t f) = (term231 A t).
Proof. exact (MK_COMB (@lem3758634) (@lem3758633 A t f h1)). Qed.
Lemma lem3758638 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term172 A t s) = (term172 A t s).
Proof. exact (eq_refl (term172 A t s)). Qed.
Lemma lem3758639 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term257 A f t s) = (term230 A t s).
Proof. exact (MK_COMB (@lem3758635 A t f h1) (@lem3758638 A t s)). Qed.
Lemma lem3758642 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term255 A f s) = (term228 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3758639 A t s f h1)). Qed.
Lemma lem3758643 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3758644 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term265 A f s) = (term241 A s).
Proof. exact (MK_COMB (@lem3758643 A) (@lem3758642 A s f h1)). Qed.
Lemma lem3758649 {A : Type'} (s : A -> Prop) : (term333 A s) = (term333 A s).
Proof. exact (eq_refl (term333 A s)). Qed.
Lemma lem3758650 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term334 A f s) = (term402 A s).
Proof. exact (MK_COMB (@lem3758649 A s) (@lem3758644 A s f h1)). Qed.
Lemma lem3758653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3758654 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term335 A f s) = (term403 A s).
Proof. exact (MK_COMB (@lem3758653) (@lem3758650 A s f h1)). Qed.
Lemma lem3758664 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3758665 {A : Type'} (s' : A -> Prop) : (@IN (A -> Prop) s') = (@IN (A -> Prop) s').
Proof. exact (eq_refl (@IN (A -> Prop) s')). Qed.
Lemma lem3758666 {A : Type'} (s' : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@IN (A -> Prop) s' f) = (@IN (A -> Prop) s' (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3758665 A s') (@lem3758664 A f h1)). Qed.
Lemma lem3758667 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3758668 {A : Type'} (s' : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term258 A s' f) = (term231 A s').
Proof. exact (MK_COMB (@lem3758667) (@lem3758666 A s' f h1)). Qed.
Lemma lem3758671 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term172 A s s') = (term172 A s s').
Proof. exact (eq_refl (term172 A s s')). Qed.
Lemma lem3758672 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term365 A f s s') = (term404 A s s').
Proof. exact (MK_COMB (@lem3758668 A s' f h1) (@lem3758671 A s s')). Qed.
Lemma lem3758675 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term363 A f s) = (term405 A s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3758672 A s s' f h1)). Qed.
Lemma lem3758676 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3758677 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term375 A f s) = (term406 A s).
Proof. exact (MK_COMB (@lem3758676 A) (@lem3758675 A s f h1)). Qed.
Lemma lem3758682 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3758683 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term377 A f s) = (term407 A s).
Proof. exact (MK_COMB (@lem3758682) (@lem3758677 A s f h1)). Qed.
Lemma lem3758691 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3758692 {A : Type'} (s : A -> Prop) : (@IN (A -> Prop) s) = (@IN (A -> Prop) s).
Proof. exact (eq_refl (@IN (A -> Prop) s)). Qed.
Lemma lem3758693 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@IN (A -> Prop) s f) = (@IN (A -> Prop) s (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3758692 A s) (@lem3758691 A f h1)). Qed.
Lemma lem3758694 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3758695 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term258 A s f) = (term231 A s).
Proof. exact (MK_COMB (@lem3758694) (@lem3758693 A s f h1)). Qed.
Lemma lem3758703 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3758704 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t) = (@IN (A -> Prop) t).
Proof. exact (eq_refl (@IN (A -> Prop) t)). Qed.
Lemma lem3758705 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@IN (A -> Prop) t f) = (@IN (A -> Prop) t (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3758704 A t) (@lem3758703 A f h1)). Qed.
Lemma lem3758706 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3758707 {A : Type'} (t : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term258 A t f) = (term231 A t).
Proof. exact (MK_COMB (@lem3758706) (@lem3758705 A t f h1)). Qed.
Lemma lem3758710 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term172 A t s) = (term172 A t s).
Proof. exact (eq_refl (term172 A t s)). Qed.
Lemma lem3758711 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term257 A f t s) = (term230 A t s).
Proof. exact (MK_COMB (@lem3758707 A t f h1) (@lem3758710 A t s)). Qed.
Lemma lem3758714 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term255 A f s) = (term228 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3758711 A t s f h1)). Qed.
Lemma lem3758715 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3758716 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term265 A f s) = (term241 A s).
Proof. exact (MK_COMB (@lem3758715 A) (@lem3758714 A s f h1)). Qed.
Lemma lem3758721 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term266 A f s) = (term242 A s).
Proof. exact (MK_COMB (@lem3758695 A s f h1) (@lem3758716 A s f h1)). Qed.
Lemma lem3758724 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term267 A f) = (term244 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3758721 A s f h1)). Qed.
Lemma lem3758725 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3758726 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term268 A f) = (term246 A).
Proof. exact (MK_COMB (@lem3758725 A) (@lem3758724 A f h1)). Qed.
Lemma lem3758731 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term380 A s f) = (term408 A s).
Proof. exact (MK_COMB (@lem3758683 A s f h1) (@lem3758726 A f h1)). Qed.
Lemma lem3758734 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term381 A s f) = (term409 A s).
Proof. exact (MK_COMB (@lem3758654 A s f h1) (@lem3758731 A s f h1)). Qed.
Lemma lem3758737 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3758738 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term382 A s f) = (term410 A s).
Proof. exact (MK_COMB (@lem3758737) (@lem3758734 A s f h1)). Qed.
Lemma lem3758740 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term397 A x y s) = (term398 A y x s).
Proof. exact (EQ_MP (@lem3758518 A y x s) (@lem3758517 A y x s)). Qed.
Lemma lem3758741 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : type686 A) : (term275 A x y s) = (term411 A y x s).
Proof. exact (@lem3758740 (A -> Prop) y x s). Qed.
Lemma lem3758742 {A : Type'} (s : A -> Prop) (f : type686 A) : (term344 A s f) = (term412 A s f).
Proof. exact (@lem3758741 A s (term340 A s f) f). Qed.
Lemma lem3758748 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3758749 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem3758750 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@UNIONS A f) = (@UNIONS A (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3758749 A) (@lem3758748 A f h1)). Qed.
Lemma lem3758752 {_86801 : Type'} : (@UNIONS _86801 (@EMPTY (_86801 -> Prop))) = (@EMPTY _86801).
Proof. exact (EQ_MP (@lem3322101 _86801) (@lem3322164 _86801)). Qed.
Lemma lem3758753 {A : Type'} : (@UNIONS A (@EMPTY (A -> Prop))) = (@EMPTY A).
Proof. exact (@lem3758752 A). Qed.
Lemma lem3758754 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@UNIONS A f) = (@EMPTY A).
Proof. exact (TRANS (@lem3758750 A f h1) (@lem3758753 A)). Qed.
Lemma lem3758755 {A : Type'} (s : A -> Prop) : (@UNION A s) = (@UNION A s).
Proof. exact (eq_refl (@UNION A s)). Qed.
Lemma lem3758756 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term340 A s f) = (@UNION A s (@EMPTY A)).
Proof. exact (MK_COMB (@lem3758755 A s) (@lem3758754 A f h1)). Qed.
Lemma lem3758758 {A : Type'} (s : A -> Prop) : (@UNION A s (@EMPTY A)) = s.
Proof. exact (EQ_MP (@lem3758505 A s) (@lem3758504 A s)). Qed.
Lemma lem3758759 {A : Type'} (s : A -> Prop) : (@UNION A s (@EMPTY A)) = s.
Proof. exact (@lem3758758 A s). Qed.
Lemma lem3758760 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term340 A s f) = s.
Proof. exact (TRANS (@lem3758756 A s f h1) (@lem3758759 A s)). Qed.
Lemma lem3758761 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3758762 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term413 A s f) = (@eq (A -> Prop) s).
Proof. exact (MK_COMB (@lem3758761 A) (@lem3758760 A s f h1)). Qed.
Lemma lem3758763 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3758764 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : ((term340 A s f) = s) = (s = s).
Proof. exact (MK_COMB (@lem3758762 A s f h1) (@lem3758763 A s)). Qed.
Lemma lem3758766 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3758767 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem3758766 (A -> Prop) x). Qed.
Lemma lem3758768 {A : Type'} (s : A -> Prop) : (s = s) = True.
Proof. exact (@lem3758767 A s). Qed.
Lemma lem3758769 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : ((term340 A s f) = s) = True.
Proof. exact (TRANS (@lem3758764 A s f h1) (@lem3758768 A s)). Qed.
Lemma lem3758770 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3758771 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term414 A f s) = (or True).
Proof. exact (MK_COMB (@lem3758770) (@lem3758769 A s f h1)). Qed.
Lemma lem3758773 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3758774 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem3758775 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@UNIONS A f) = (@UNIONS A (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3758774 A) (@lem3758773 A f h1)). Qed.
Lemma lem3758777 {_86801 : Type'} : (@UNIONS _86801 (@EMPTY (_86801 -> Prop))) = (@EMPTY _86801).
Proof. exact (EQ_MP (@lem3322101 _86801) (@lem3322164 _86801)). Qed.
Lemma lem3758778 {A : Type'} : (@UNIONS A (@EMPTY (A -> Prop))) = (@EMPTY A).
Proof. exact (@lem3758777 A). Qed.
Lemma lem3758779 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (@UNIONS A f) = (@EMPTY A).
Proof. exact (TRANS (@lem3758775 A f h1) (@lem3758778 A)). Qed.
Lemma lem3758780 {A : Type'} (s : A -> Prop) : (@UNION A s) = (@UNION A s).
Proof. exact (eq_refl (@UNION A s)). Qed.
Lemma lem3758781 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term340 A s f) = (@UNION A s (@EMPTY A)).
Proof. exact (MK_COMB (@lem3758780 A s) (@lem3758779 A f h1)). Qed.
Lemma lem3758783 {A : Type'} (s : A -> Prop) : (@UNION A s (@EMPTY A)) = s.
Proof. exact (EQ_MP (@lem3758505 A s) (@lem3758504 A s)). Qed.
Lemma lem3758784 {A : Type'} (s : A -> Prop) : (@UNION A s (@EMPTY A)) = s.
Proof. exact (@lem3758783 A s). Qed.
Lemma lem3758785 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term340 A s f) = s.
Proof. exact (TRANS (@lem3758781 A s f h1) (@lem3758784 A s)). Qed.
Lemma lem3758786 {A : Type'} : (@IN (A -> Prop)) = (@IN (A -> Prop)).
Proof. exact (eq_refl (@IN (A -> Prop))). Qed.
Lemma lem3758787 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term342 A s f) = (@IN (A -> Prop) s).
Proof. exact (MK_COMB (@lem3758786 A) (@lem3758785 A s f h1)). Qed.
Lemma lem3758789 {A : Type'} (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : f = (@EMPTY (A -> Prop)).
Proof. exact (h1). Qed.
Lemma lem3758790 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term415 A s f) = (@IN (A -> Prop) s (@EMPTY (A -> Prop))).
Proof. exact (MK_COMB (@lem3758787 A s f h1) (@lem3758789 A f h1)). Qed.
Lemma lem3758791 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term412 A s f) = (term416 A s).
Proof. exact (MK_COMB (@lem3758771 A s f h1) (@lem3758790 A s f h1)). Qed.
Lemma lem3758793 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem3758794 {A : Type'} (s : A -> Prop) : (term416 A s) = True.
Proof. exact (@lem3758793 (@IN (A -> Prop) s (@EMPTY (A -> Prop)))). Qed.
Lemma lem3758795 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term412 A s f) = True.
Proof. exact (TRANS (@lem3758791 A s f h1) (@lem3758794 A s)). Qed.
Lemma lem3758796 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term344 A s f) = True.
Proof. exact (TRANS (@lem3758742 A s f) (@lem3758795 A s f h1)). Qed.
Lemma lem3758797 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term383 A s f) = (term417 A s).
Proof. exact (MK_COMB (@lem3758738 A s f h1) (@lem3758796 A s f h1)). Qed.
Lemma lem3758799 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3758800 {A : Type'} (s : A -> Prop) : (term417 A s) = True.
Proof. exact (@lem3758799 (term409 A s)). Qed.
Lemma lem3758801 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term383 A s f) = True.
Proof. exact (TRANS (@lem3758797 A s f h1) (@lem3758800 A s)). Qed.
Lemma lem3758802 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term385 A s f) = (True -> True).
Proof. exact (MK_COMB (@lem3758617 A f h1) (@lem3758801 A s f h1)). Qed.
Lemma lem3758804 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3758805 : (True -> True) = True.
Proof. exact (@lem3758804 True). Qed.
Lemma lem3758806 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : (term385 A s f) = True.
Proof. exact (TRANS (@lem3758802 A s f h1) (@lem3758805)). Qed.
Lemma lem3758807 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : True = (term385 A s f).
Proof. exact (SYM (@lem3758806 A s f h1)). Qed.
Lemma lem3758808 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : f = (@EMPTY (A -> Prop))) : term385 A s f.
Proof. exact (EQ_MP (@lem3758807 A s f h1) (@lem0)). Qed.
Lemma lem3758817 {A : Type'} (x : A) : term392 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3758818 {A : Type'} (x : A) : (term392 A x) = (term393 A x).
Proof. exact (eq_refl (term392 A x)). Qed.
Lemma lem3758819 {A : Type'} (x : A) : term393 A x.
Proof. exact (EQ_MP (@lem3758818 A x) (@lem3758817 A x)). Qed.
Lemma lem3758820 {A : Type'} (x : A) (y : A) : term394 A x y.
Proof. exact (@lem3758819 A x y). Qed.
Lemma lem3758821 {A : Type'} (y : A) (x : A) : (term394 A x y) = (term395 A y x).
Proof. exact (eq_refl (term394 A x y)). Qed.
Lemma lem3758822 {A : Type'} (y : A) (x : A) : term395 A y x.
Proof. exact (EQ_MP (@lem3758821 A y x) (@lem3758820 A x y)). Qed.
Lemma lem3758823 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term396 A y x s.
Proof. exact (@lem3758822 A y x s). Qed.
Lemma lem3758824 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term396 A y x s) = ((term397 A x y s) = (term398 A y x s)).
Proof. exact (eq_refl (term396 A y x s)). Qed.
Lemma lem3758826 {A : Type'} (f : type686 A) : term418 A f.
Proof. exact (@lem82 (f = (@EMPTY (A -> Prop)))). Qed.
Lemma lem3758844 {A : Type'} (f : type686 A) (h1 : term112 A f) : (f = (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3758826 A f (@lem3757300 A f h1)). Qed.
Lemma lem3758845 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3758846 {A : Type'} (f : type686 A) (h1 : term112 A f) : (term112 A f) = (~ False).
Proof. exact (MK_COMB (@lem3758845) (@lem3758844 A f h1)). Qed.
Lemma lem3758848 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3758849 {A : Type'} (f : type686 A) (h1 : term112 A f) : (term112 A f) = True.
Proof. exact (TRANS (@lem3758846 A f h1) (@lem3758848)). Qed.
Lemma lem3758850 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3758851 {A : Type'} (f : type686 A) (h1 : term112 A f) : (term184 A f) = (imp True).
Proof. exact (MK_COMB (@lem3758850) (@lem3758849 A f h1)). Qed.
Lemma lem3758868 {A : Type'} (f : type686 A) : (term270 A f) = (term270 A f).
Proof. exact (eq_refl (term270 A f)). Qed.
Lemma lem3758869 {A : Type'} (f : type686 A) (h1 : term112 A f) : (term271 A f) = (term419 A f).
Proof. exact (MK_COMB (@lem3758851 A f h1) (@lem3758868 A f)). Qed.
Lemma lem3758871 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3758872 {A : Type'} (f : type686 A) : (term419 A f) = (term270 A f).
Proof. exact (@lem3758871 (term270 A f)). Qed.
Lemma lem3758889 {A : Type'} (f : type686 A) (h1 : term112 A f) : (term271 A f) = (term270 A f).
Proof. exact (TRANS (@lem3758869 A f h1) (@lem3758872 A f)). Qed.
Lemma lem3758890 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3758891 {A : Type'} (f : type686 A) (h1 : term112 A f) : (term272 A f) = (term420 A f).
Proof. exact (MK_COMB (@lem3758890) (@lem3758889 A f h1)). Qed.
Lemma lem3758931 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term397 A x y s) = (term398 A y x s).
Proof. exact (EQ_MP (@lem3758824 A y x s) (@lem3758823 A y x s)). Qed.
Lemma lem3758932 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : type686 A) : (term275 A x y s) = (term411 A y x s).
Proof. exact (@lem3758931 (A -> Prop) y x s). Qed.
Lemma lem3758933 {A : Type'} (s : A -> Prop) (f : type686 A) : (term344 A s f) = (term412 A s f).
Proof. exact (@lem3758932 A s (term340 A s f) f). Qed.
Lemma lem3758938 {A : Type'} (s : A -> Prop) (f : type686 A) : (term382 A s f) = (term382 A s f).
Proof. exact (eq_refl (term382 A s f)). Qed.
Lemma lem3758939 {A : Type'} (s : A -> Prop) (f : type686 A) : (term383 A s f) = (term421 A s f).
Proof. exact (MK_COMB (@lem3758938 A s f) (@lem3758933 A s f)). Qed.
Lemma lem3758942 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) : (term385 A s f) = (term422 A s f).
Proof. exact (MK_COMB (@lem3758891 A f h1) (@lem3758939 A s f)). Qed.
Lemma lem3758945 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) : (term422 A s f) = (term385 A s f).
Proof. exact (SYM (@lem3758942 A s f h1)). Qed.
Lemma lem3758946 {A : Type'} (f : type686 A) (h1 : term270 A f) : term270 A f.
Proof. exact (h1). Qed.
Lemma lem3758947 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term381 A s f) : term381 A s f.
Proof. exact (h1). Qed.
Lemma lem3758948 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term380 A s f) : term380 A s f.
Proof. exact (h1). Qed.
Lemma lem3758949 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term334 A f s) : term334 A f s.
Proof. exact (h1). Qed.
Lemma lem3758950 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term265 A f s) : term265 A f s.
Proof. exact (h1). Qed.
Lemma lem3758951 {A : Type'} (s : A -> Prop) (h1 : @SUBSET A s s) : @SUBSET A s s.
Proof. exact (h1). Qed.
Lemma lem3758952 {A : Type'} (f : type686 A) (h1 : term268 A f) : term268 A f.
Proof. exact (h1). Qed.
Lemma lem3758953 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term375 A f s) : term375 A f s.
Proof. exact (h1). Qed.
Lemma lem3758979 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term268 A f) : term368 A f s.
Proof. exact (@lem3758952 A f h1 s). Qed.
Lemma lem3758980 {A : Type'} (f : type686 A) (s : A -> Prop) : (term368 A f s) = (term266 A f s).
Proof. exact (eq_refl (term368 A f s)). Qed.
Lemma lem3758981 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term268 A f) : term266 A f s.
Proof. exact (EQ_MP (@lem3758980 A f s) (@lem3758979 A s f h1)). Qed.
Lemma lem3758982 {A : Type'} (f : type686 A) (s : A -> Prop) : (term266 A f s) = ((term266 A f s) = True).
Proof. exact (@lem7 (term266 A f s)). Qed.
Lemma lem3758993 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term268 A f) : (term266 A f s) = True.
Proof. exact (EQ_MP (@lem3758982 A f s) (@lem3758981 A s f h1)). Qed.
Lemma lem3758994 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term268 A f) : (term266 A f s) = True.
Proof. exact (@lem3758993 A s f h1). Qed.
Lemma lem3758995 {A : Type'} (f : type686 A) (h1 : term268 A f) : (term267 A f) = (term423 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3758994 A s f h1)). Qed.
Lemma lem3758996 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3758997 {A : Type'} (f : type686 A) (h1 : term268 A f) : (term268 A f) = (term424 A).
Proof. exact (MK_COMB (@lem3758996 A) (@lem3758995 A f h1)). Qed.
Lemma lem3758999 {A : Type'} (t : Prop) : (term425 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3759000 {A : Type'} (t : Prop) : (term426 A t) = t.
Proof. exact (@lem3758999 (A -> Prop) t). Qed.
Lemma lem3759001 {A : Type'} : (term424 A) = True.
Proof. exact (@lem3759000 A True). Qed.
Lemma lem3759002 {A : Type'} (f : type686 A) (h1 : term268 A f) : (term268 A f) = True.
Proof. exact (TRANS (@lem3758997 A f h1) (@lem3759001 A)). Qed.
Lemma lem3759003 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3759004 {A : Type'} (f : type686 A) (h1 : term268 A f) : (term269 A f) = (imp True).
Proof. exact (MK_COMB (@lem3759003) (@lem3759002 A f h1)). Qed.
Lemma lem3759005 {A : Type'} (f : type686 A) : (term166 A f) = (term166 A f).
Proof. exact (eq_refl (term166 A f)). Qed.
Lemma lem3759006 {A : Type'} (f : type686 A) (h1 : term268 A f) : (term270 A f) = (term427 A f).
Proof. exact (MK_COMB (@lem3759004 A f h1) (@lem3759005 A f)). Qed.
Lemma lem3759008 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3759009 {A : Type'} (f : type686 A) : (term427 A f) = (term166 A f).
Proof. exact (@lem3759008 (term166 A f)). Qed.
Lemma lem3759010 {A : Type'} (f : type686 A) (h1 : term268 A f) : (term270 A f) = (term166 A f).
Proof. exact (TRANS (@lem3759006 A f h1) (@lem3759009 A f)). Qed.
Lemma lem3759011 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3759012 {A : Type'} (f : type686 A) (h1 : term268 A f) : (term420 A f) = (term428 A f).
Proof. exact (MK_COMB (@lem3759011) (@lem3759010 A f h1)). Qed.
Lemma lem3759017 {A : Type'} (s : A -> Prop) (f : type686 A) : (term412 A s f) = (term412 A s f).
Proof. exact (eq_refl (term412 A s f)). Qed.
Lemma lem3759018 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term268 A f) : (term429 A s f) = (term430 A s f).
Proof. exact (MK_COMB (@lem3759012 A f h1) (@lem3759017 A s f)). Qed.
Lemma lem3759021 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term268 A f) : (term430 A s f) = (term429 A s f).
Proof. exact (SYM (@lem3759018 A s f h1)). Qed.
Lemma lem3759023 {_98208 : Type'} (s : _98208 -> Prop) (t : _98208 -> Prop) (f : type686 _98208) : term1 _98208 s t f.
Proof. exact (@lem3757294 _98208 s t f (@lem3757286 _98208 s t f)). Qed.
Lemma lem3759024 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : type686 A) : term1 A s t f.
Proof. exact (@lem3759023 A s t f). Qed.
Lemma lem3759025 {A : Type'} (s : A -> Prop) (f : type686 A) : term431 A s f.
Proof. exact (@lem3759024 A s (@UNIONS A f) f). Qed.
Lemma lem3759026 (t1 : Prop) : term432 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3759027 (t1 : Prop) : (term432 t1) = (term433 t1).
Proof. exact (eq_refl (term432 t1)). Qed.
Lemma lem3759028 (t1 : Prop) : term433 t1.
Proof. exact (EQ_MP (@lem3759027 t1) (@lem3759026 t1)). Qed.
Lemma lem3759029 (t1 : Prop) (t2 : Prop) : term434 t1 t2.
Proof. exact (@lem3759028 t1 t2). Qed.
Lemma lem3759030 (t1 : Prop) (t2 : Prop) : (term434 t1 t2) = (term435 t1 t2).
Proof. exact (eq_refl (term434 t1 t2)). Qed.
Lemma lem3759031 (t1 : Prop) (t2 : Prop) : term435 t1 t2.
Proof. exact (EQ_MP (@lem3759030 t1 t2) (@lem3759029 t1 t2)). Qed.
Lemma lem3759032 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term436 t1 t2 t3.
Proof. exact (@lem3759031 t1 t2 t3). Qed.
Lemma lem3759033 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term436 t1 t2 t3) = ((term51 t1 t2 t3) = (term437 t1 t2 t3)).
Proof. exact (eq_refl (term436 t1 t2 t3)). Qed.
Lemma lem3759034 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term51 t1 t2 t3) = (term437 t1 t2 t3).
Proof. exact (EQ_MP (@lem3759033 t1 t2 t3) (@lem3759032 t1 t2 t3)). Qed.
Lemma lem3759035 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term437 t1 t2 t3) = (term51 t1 t2 t3).
Proof. exact (SYM (@lem3759034 t1 t2 t3)). Qed.
Lemma lem3759036 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term112 A f) (h2 : @SUBSET A s s) : term438 A s f.
Proof. exact (conj (@lem3758951 A s h2) (@lem3757300 A f h1)). Qed.
Lemma lem3759037 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term265 A f s) (h2 : term112 A f) (h3 : @SUBSET A s s) : term439 A s f.
Proof. exact (conj (@lem3758950 A f s h1) (@lem3759036 A f s h2 h3)). Qed.
Lemma lem3759038 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term375 A f s) (h2 : term265 A f s) (h3 : term112 A f) (h4 : @SUBSET A s s) : term440 A s f.
Proof. exact (conj (@lem3758953 A f s h1) (@lem3759037 A f s h2 h3 h4)). Qed.
Lemma lem3759039 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : @SUBSET A s s) : term441 A s f.
Proof. exact (conj (@lem3758952 A f h1) (@lem3759038 A f s h2 h3 h4 h5)). Qed.
Lemma lem3759059 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3759060 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (@lem3759059 A s t). Qed.
Lemma lem3759067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3759068 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term443 A s t) = (term444 A s t).
Proof. exact (MK_COMB (@lem3759067) (@lem3759060 A s t)). Qed.
Lemma lem3759070 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3759071 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (@lem3759070 A s t). Qed.
Lemma lem3759072 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term442 A t s).
Proof. exact (@lem3759071 A t s). Qed.
Lemma lem3759079 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term172 A t s) = (term445 A t s).
Proof. exact (MK_COMB (@lem3759068 A s t) (@lem3759072 A t s)). Qed.
Lemma lem3759082 {A : Type'} (t : A -> Prop) (f : type686 A) : (term258 A t f) = (term258 A t f).
Proof. exact (eq_refl (term258 A t f)). Qed.
Lemma lem3759083 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term257 A f t s) = (term446 A f t s).
Proof. exact (MK_COMB (@lem3759082 A t f) (@lem3759079 A t s)). Qed.
Lemma lem3759086 {A : Type'} (f : type686 A) (s : A -> Prop) : (term255 A f s) = (term447 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3759083 A f t s)). Qed.
Lemma lem3759087 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3759088 {A : Type'} (f : type686 A) (s : A -> Prop) : (term265 A f s) = (term448 A f s).
Proof. exact (MK_COMB (@lem3759087 A) (@lem3759086 A f s)). Qed.
Lemma lem3759093 {A : Type'} (s : A -> Prop) (f : type686 A) : (term258 A s f) = (term258 A s f).
Proof. exact (eq_refl (term258 A s f)). Qed.
Lemma lem3759094 {A : Type'} (f : type686 A) (s : A -> Prop) : (term266 A f s) = (term449 A f s).
Proof. exact (MK_COMB (@lem3759093 A s f) (@lem3759088 A f s)). Qed.
Lemma lem3759097 {A : Type'} (f : type686 A) : (term267 A f) = (term450 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3759094 A f s)). Qed.
Lemma lem3759098 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3759099 {A : Type'} (f : type686 A) : (term268 A f) = (term451 A f).
Proof. exact (MK_COMB (@lem3759098 A) (@lem3759097 A f)). Qed.
Lemma lem3759104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3759105 {A : Type'} (f : type686 A) : (term452 A f) = (term453 A f).
Proof. exact (MK_COMB (@lem3759104) (@lem3759099 A f)). Qed.
Lemma lem3759117 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3759118 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (@lem3759117 A s t). Qed.
Lemma lem3759119 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (@SUBSET A s' s) = (term442 A s' s).
Proof. exact (@lem3759118 A s' s). Qed.
Lemma lem3759126 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3759127 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term443 A s' s) = (term444 A s' s).
Proof. exact (MK_COMB (@lem3759126) (@lem3759119 A s' s)). Qed.
Lemma lem3759129 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3759130 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (@lem3759129 A s t). Qed.
Lemma lem3759131 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (@SUBSET A s s') = (term442 A s s').
Proof. exact (@lem3759130 A s s'). Qed.
Lemma lem3759138 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term172 A s s') = (term445 A s s').
Proof. exact (MK_COMB (@lem3759127 A s' s) (@lem3759131 A s s')). Qed.
Lemma lem3759141 {A : Type'} (s' : A -> Prop) (f : type686 A) : (term258 A s' f) = (term258 A s' f).
Proof. exact (eq_refl (term258 A s' f)). Qed.
Lemma lem3759142 {A : Type'} (f : type686 A) (s : A -> Prop) (s' : A -> Prop) : (term365 A f s s') = (term454 A f s s').
Proof. exact (MK_COMB (@lem3759141 A s' f) (@lem3759138 A s s')). Qed.
Lemma lem3759145 {A : Type'} (f : type686 A) (s : A -> Prop) : (term363 A f s) = (term455 A f s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3759142 A f s s')). Qed.
Lemma lem3759146 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3759147 {A : Type'} (f : type686 A) (s : A -> Prop) : (term375 A f s) = (term456 A f s).
Proof. exact (MK_COMB (@lem3759146 A) (@lem3759145 A f s)). Qed.
Lemma lem3759152 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3759153 {A : Type'} (f : type686 A) (s : A -> Prop) : (term377 A f s) = (term457 A f s).
Proof. exact (MK_COMB (@lem3759152) (@lem3759147 A f s)). Qed.
Lemma lem3759165 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3759166 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (@lem3759165 A s t). Qed.
Lemma lem3759173 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3759174 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term443 A s t) = (term444 A s t).
Proof. exact (MK_COMB (@lem3759173) (@lem3759166 A s t)). Qed.
Lemma lem3759176 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3759177 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (@lem3759176 A s t). Qed.
Lemma lem3759178 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term442 A t s).
Proof. exact (@lem3759177 A t s). Qed.
Lemma lem3759185 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term172 A t s) = (term445 A t s).
Proof. exact (MK_COMB (@lem3759174 A s t) (@lem3759178 A t s)). Qed.
Lemma lem3759188 {A : Type'} (t : A -> Prop) (f : type686 A) : (term258 A t f) = (term258 A t f).
Proof. exact (eq_refl (term258 A t f)). Qed.
Lemma lem3759189 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term257 A f t s) = (term446 A f t s).
Proof. exact (MK_COMB (@lem3759188 A t f) (@lem3759185 A t s)). Qed.
Lemma lem3759192 {A : Type'} (f : type686 A) (s : A -> Prop) : (term255 A f s) = (term447 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3759189 A f t s)). Qed.
Lemma lem3759193 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3759194 {A : Type'} (f : type686 A) (s : A -> Prop) : (term265 A f s) = (term448 A f s).
Proof. exact (MK_COMB (@lem3759193 A) (@lem3759192 A f s)). Qed.
Lemma lem3759199 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3759200 {A : Type'} (f : type686 A) (s : A -> Prop) : (term458 A f s) = (term459 A f s).
Proof. exact (MK_COMB (@lem3759199) (@lem3759194 A f s)). Qed.
Lemma lem3759204 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3759205 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term442 A s t).
Proof. exact (@lem3759204 A s t). Qed.
Lemma lem3759206 {A : Type'} (s : A -> Prop) : (@SUBSET A s s) = (term460 A s).
Proof. exact (@lem3759205 A s s). Qed.
Lemma lem3759212 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3759213 {A : Type'} (x : A) (s : A -> Prop) : (term461 A x s) = True.
Proof. exact (@lem3759212 (@IN A x s)). Qed.
Lemma lem3759214 {A : Type'} (s : A -> Prop) : (term462 A s) = (term463 A).
Proof. exact (fun_ext (fun x : A => @lem3759213 A x s)). Qed.
Lemma lem3759215 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3759216 {A : Type'} (s : A -> Prop) : (term460 A s) = (term464 A).
Proof. exact (MK_COMB (@lem3759215 A) (@lem3759214 A s)). Qed.
Lemma lem3759218 {A : Type'} (t : Prop) : (term425 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3759219 {A : Type'} (t : Prop) : (term425 A t) = t.
Proof. exact (@lem3759218 A t). Qed.
Lemma lem3759220 {A : Type'} : (term464 A) = True.
Proof. exact (@lem3759219 A True). Qed.
Lemma lem3759221 {A : Type'} (s : A -> Prop) : (term460 A s) = True.
Proof. exact (TRANS (@lem3759216 A s) (@lem3759220 A)). Qed.
Lemma lem3759222 {A : Type'} (s : A -> Prop) : (@SUBSET A s s) = True.
Proof. exact (TRANS (@lem3759206 A s) (@lem3759221 A s)). Qed.
Lemma lem3759223 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3759224 {A : Type'} (s : A -> Prop) : (term333 A s) = (and True).
Proof. exact (MK_COMB (@lem3759223) (@lem3759222 A s)). Qed.
Lemma lem3759228 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term465 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3759229 {A : Type'} (s : type686 A) (t : type686 A) : (s = t) = (term466 A s t).
Proof. exact (@lem3759228 (A -> Prop) s t). Qed.
Lemma lem3759230 {A : Type'} (f : type686 A) : (f = (@EMPTY (A -> Prop))) = (term467 A f).
Proof. exact (@lem3759229 A f (@EMPTY (A -> Prop))). Qed.
Lemma lem3759239 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3759240 {A : Type'} (f : type686 A) : (term112 A f) = (term468 A f).
Proof. exact (MK_COMB (@lem3759239) (@lem3759230 A f)). Qed.
Lemma lem3759241 {A : Type'} (s : A -> Prop) (f : type686 A) : (term438 A s f) = (term469 A f).
Proof. exact (MK_COMB (@lem3759224 A s) (@lem3759240 A f)). Qed.
Lemma lem3759243 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3759244 {A : Type'} (f : type686 A) : (term469 A f) = (term468 A f).
Proof. exact (@lem3759243 (term468 A f)). Qed.
Lemma lem3759253 {A : Type'} (s : A -> Prop) (f : type686 A) : (term438 A s f) = (term468 A f).
Proof. exact (TRANS (@lem3759241 A s f) (@lem3759244 A f)). Qed.
Lemma lem3759254 {A : Type'} (s : A -> Prop) (f : type686 A) : (term439 A s f) = (term470 A s f).
Proof. exact (MK_COMB (@lem3759200 A f s) (@lem3759253 A s f)). Qed.
Lemma lem3759257 {A : Type'} (s : A -> Prop) (f : type686 A) : (term440 A s f) = (term471 A s f).
Proof. exact (MK_COMB (@lem3759153 A f s) (@lem3759254 A s f)). Qed.
Lemma lem3759260 {A : Type'} (s : A -> Prop) (f : type686 A) : (term441 A s f) = (term472 A s f).
Proof. exact (MK_COMB (@lem3759105 A f) (@lem3759257 A s f)). Qed.
Lemma lem3759263 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3759264 {A : Type'} (s : A -> Prop) (f : type686 A) : (term473 A s f) = (term474 A s f).
Proof. exact (MK_COMB (@lem3759263) (@lem3759260 A s f)). Qed.
Lemma lem3759270 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term465 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3759271 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term465 A s t).
Proof. exact (@lem3759270 A s t). Qed.
Lemma lem3759272 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term340 A s f) = s) = (term475 A f s).
Proof. exact (@lem3759271 A (term340 A s f) s). Qed.
Lemma lem3759281 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3759282 {A : Type'} (f : type686 A) (s : A -> Prop) : (term414 A f s) = (term476 A f s).
Proof. exact (MK_COMB (@lem3759281) (@lem3759272 A f s)). Qed.
Lemma lem3759286 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term465 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3759287 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term465 A s t).
Proof. exact (@lem3759286 A s t). Qed.
Lemma lem3759288 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term340 A s f) = (@UNIONS A f)) = (term477 A s f).
Proof. exact (@lem3759287 A (term340 A s f) (@UNIONS A f)). Qed.
Lemma lem3759297 {A : Type'} (s : A -> Prop) (f : type686 A) : (term478 A s f) = (term479 A s f).
Proof. exact (MK_COMB (@lem3759282 A f s) (@lem3759288 A s f)). Qed.
Lemma lem3759300 {A : Type'} (s : A -> Prop) (f : type686 A) : (term480 A s f) = (term481 A s f).
Proof. exact (MK_COMB (@lem3759264 A s f) (@lem3759297 A s f)). Qed.
Lemma lem3759303 {A : Type'} (s : A -> Prop) (f : type686 A) : (term481 A s f) = (term480 A s f).
Proof. exact (SYM (@lem3759300 A s f)). Qed.
Lemma lem3759315 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759316 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3759315 (A -> Prop) P x). Qed.
Lemma lem3759317 {A : Type'} (f : type686 A) (s : A -> Prop) : (@IN (A -> Prop) s f) = (f s).
Proof. exact (@lem3759316 A f s). Qed.
Lemma lem3759318 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3759319 {A : Type'} (f : type686 A) (s : A -> Prop) : (term258 A s f) = (term482 A f s).
Proof. exact (MK_COMB (@lem3759318) (@lem3759317 A f s)). Qed.
Lemma lem3759327 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759328 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3759327 (A -> Prop) P x). Qed.
Lemma lem3759329 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3759328 A f t). Qed.
Lemma lem3759330 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3759331 {A : Type'} (f : type686 A) (t : A -> Prop) : (term258 A t f) = (term482 A f t).
Proof. exact (MK_COMB (@lem3759330) (@lem3759329 A f t)). Qed.
Lemma lem3759341 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759342 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759341 A P x). Qed.
Lemma lem3759343 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3759342 A s x). Qed.
Lemma lem3759344 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3759345 {A : Type'} (s : A -> Prop) (x : A) : (term483 A x s) = (term484 A s x).
Proof. exact (MK_COMB (@lem3759344) (@lem3759343 A s x)). Qed.
Lemma lem3759347 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759348 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759347 A P x). Qed.
Lemma lem3759349 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3759348 A t x). Qed.
Lemma lem3759350 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term485 A s x t) = (term486 A s t x).
Proof. exact (MK_COMB (@lem3759345 A s x) (@lem3759349 A t x)). Qed.
Lemma lem3759353 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term487 A s t) = (term488 A s t).
Proof. exact (fun_ext (fun x : A => @lem3759350 A s t x)). Qed.
Lemma lem3759354 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3759355 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term442 A s t) = (term489 A s t).
Proof. exact (MK_COMB (@lem3759354 A) (@lem3759353 A s t)). Qed.
Lemma lem3759360 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3759361 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term444 A s t) = (term490 A s t).
Proof. exact (MK_COMB (@lem3759360) (@lem3759355 A s t)). Qed.
Lemma lem3759369 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759370 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759369 A P x). Qed.
Lemma lem3759371 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3759370 A t x). Qed.
Lemma lem3759372 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3759373 {A : Type'} (t : A -> Prop) (x : A) : (term483 A x t) = (term484 A t x).
Proof. exact (MK_COMB (@lem3759372) (@lem3759371 A t x)). Qed.
Lemma lem3759375 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759376 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759375 A P x). Qed.
Lemma lem3759377 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3759376 A s x). Qed.
Lemma lem3759378 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term485 A t x s) = (term486 A t s x).
Proof. exact (MK_COMB (@lem3759373 A t x) (@lem3759377 A s x)). Qed.
Lemma lem3759381 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term487 A t s) = (term488 A t s).
Proof. exact (fun_ext (fun x : A => @lem3759378 A t s x)). Qed.
Lemma lem3759382 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3759383 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term442 A t s) = (term489 A t s).
Proof. exact (MK_COMB (@lem3759382 A) (@lem3759381 A t s)). Qed.
Lemma lem3759388 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term445 A t s) = (term491 A t s).
Proof. exact (MK_COMB (@lem3759361 A s t) (@lem3759383 A t s)). Qed.
Lemma lem3759391 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term446 A f t s) = (term492 A f t s).
Proof. exact (MK_COMB (@lem3759331 A f t) (@lem3759388 A t s)). Qed.
Lemma lem3759394 {A : Type'} (f : type686 A) (s : A -> Prop) : (term447 A f s) = (term493 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3759391 A f t s)). Qed.
Lemma lem3759395 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3759396 {A : Type'} (f : type686 A) (s : A -> Prop) : (term448 A f s) = (term494 A f s).
Proof. exact (MK_COMB (@lem3759395 A) (@lem3759394 A f s)). Qed.
Lemma lem3759401 {A : Type'} (f : type686 A) (s : A -> Prop) : (term449 A f s) = (term495 A f s).
Proof. exact (MK_COMB (@lem3759319 A f s) (@lem3759396 A f s)). Qed.
Lemma lem3759404 {A : Type'} (f : type686 A) : (term450 A f) = (term496 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3759401 A f s)). Qed.
Lemma lem3759405 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3759406 {A : Type'} (f : type686 A) : (term451 A f) = (term497 A f).
Proof. exact (MK_COMB (@lem3759405 A) (@lem3759404 A f)). Qed.
Lemma lem3759411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3759412 {A : Type'} (f : type686 A) : (term453 A f) = (term498 A f).
Proof. exact (MK_COMB (@lem3759411) (@lem3759406 A f)). Qed.
Lemma lem3759422 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759423 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3759422 (A -> Prop) P x). Qed.
Lemma lem3759424 {A : Type'} (f : type686 A) (s' : A -> Prop) : (@IN (A -> Prop) s' f) = (f s').
Proof. exact (@lem3759423 A f s'). Qed.
Lemma lem3759425 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3759426 {A : Type'} (f : type686 A) (s' : A -> Prop) : (term258 A s' f) = (term482 A f s').
Proof. exact (MK_COMB (@lem3759425) (@lem3759424 A f s')). Qed.
Lemma lem3759436 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759437 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759436 A P x). Qed.
Lemma lem3759438 {A : Type'} (s' : A -> Prop) (x : A) : (@IN A x s') = (s' x).
Proof. exact (@lem3759437 A s' x). Qed.
Lemma lem3759439 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3759440 {A : Type'} (s' : A -> Prop) (x : A) : (term483 A x s') = (term484 A s' x).
Proof. exact (MK_COMB (@lem3759439) (@lem3759438 A s' x)). Qed.
Lemma lem3759442 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759443 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759442 A P x). Qed.
Lemma lem3759444 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3759443 A s x). Qed.
Lemma lem3759445 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term485 A s' x s) = (term486 A s' s x).
Proof. exact (MK_COMB (@lem3759440 A s' x) (@lem3759444 A s x)). Qed.
Lemma lem3759448 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term487 A s' s) = (term488 A s' s).
Proof. exact (fun_ext (fun x : A => @lem3759445 A s' s x)). Qed.
Lemma lem3759449 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3759450 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term442 A s' s) = (term489 A s' s).
Proof. exact (MK_COMB (@lem3759449 A) (@lem3759448 A s' s)). Qed.
Lemma lem3759455 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3759456 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term444 A s' s) = (term490 A s' s).
Proof. exact (MK_COMB (@lem3759455) (@lem3759450 A s' s)). Qed.
Lemma lem3759464 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759465 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759464 A P x). Qed.
Lemma lem3759466 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3759465 A s x). Qed.
Lemma lem3759467 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3759468 {A : Type'} (s : A -> Prop) (x : A) : (term483 A x s) = (term484 A s x).
Proof. exact (MK_COMB (@lem3759467) (@lem3759466 A s x)). Qed.
Lemma lem3759470 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759471 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759470 A P x). Qed.
Lemma lem3759472 {A : Type'} (s' : A -> Prop) (x : A) : (@IN A x s') = (s' x).
Proof. exact (@lem3759471 A s' x). Qed.
Lemma lem3759473 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term485 A s x s') = (term486 A s s' x).
Proof. exact (MK_COMB (@lem3759468 A s x) (@lem3759472 A s' x)). Qed.
Lemma lem3759476 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term487 A s s') = (term488 A s s').
Proof. exact (fun_ext (fun x : A => @lem3759473 A s s' x)). Qed.
Lemma lem3759477 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3759478 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term442 A s s') = (term489 A s s').
Proof. exact (MK_COMB (@lem3759477 A) (@lem3759476 A s s')). Qed.
Lemma lem3759483 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term445 A s s') = (term491 A s s').
Proof. exact (MK_COMB (@lem3759456 A s' s) (@lem3759478 A s s')). Qed.
Lemma lem3759486 {A : Type'} (f : type686 A) (s : A -> Prop) (s' : A -> Prop) : (term454 A f s s') = (term499 A f s s').
Proof. exact (MK_COMB (@lem3759426 A f s') (@lem3759483 A s s')). Qed.
Lemma lem3759489 {A : Type'} (f : type686 A) (s : A -> Prop) : (term455 A f s) = (term500 A f s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3759486 A f s s')). Qed.
Lemma lem3759490 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3759491 {A : Type'} (f : type686 A) (s : A -> Prop) : (term456 A f s) = (term501 A f s).
Proof. exact (MK_COMB (@lem3759490 A) (@lem3759489 A f s)). Qed.
Lemma lem3759496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3759497 {A : Type'} (f : type686 A) (s : A -> Prop) : (term457 A f s) = (term502 A f s).
Proof. exact (MK_COMB (@lem3759496) (@lem3759491 A f s)). Qed.
Lemma lem3759507 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759508 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3759507 (A -> Prop) P x). Qed.
Lemma lem3759509 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3759508 A f t). Qed.
Lemma lem3759510 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3759511 {A : Type'} (f : type686 A) (t : A -> Prop) : (term258 A t f) = (term482 A f t).
Proof. exact (MK_COMB (@lem3759510) (@lem3759509 A f t)). Qed.
Lemma lem3759521 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759522 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759521 A P x). Qed.
Lemma lem3759523 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3759522 A s x). Qed.
Lemma lem3759524 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3759525 {A : Type'} (s : A -> Prop) (x : A) : (term483 A x s) = (term484 A s x).
Proof. exact (MK_COMB (@lem3759524) (@lem3759523 A s x)). Qed.
Lemma lem3759527 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759528 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759527 A P x). Qed.
Lemma lem3759529 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3759528 A t x). Qed.
Lemma lem3759530 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term485 A s x t) = (term486 A s t x).
Proof. exact (MK_COMB (@lem3759525 A s x) (@lem3759529 A t x)). Qed.
Lemma lem3759533 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term487 A s t) = (term488 A s t).
Proof. exact (fun_ext (fun x : A => @lem3759530 A s t x)). Qed.
Lemma lem3759534 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3759535 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term442 A s t) = (term489 A s t).
Proof. exact (MK_COMB (@lem3759534 A) (@lem3759533 A s t)). Qed.
Lemma lem3759540 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3759541 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term444 A s t) = (term490 A s t).
Proof. exact (MK_COMB (@lem3759540) (@lem3759535 A s t)). Qed.
Lemma lem3759549 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759550 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759549 A P x). Qed.
Lemma lem3759551 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3759550 A t x). Qed.
Lemma lem3759552 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3759553 {A : Type'} (t : A -> Prop) (x : A) : (term483 A x t) = (term484 A t x).
Proof. exact (MK_COMB (@lem3759552) (@lem3759551 A t x)). Qed.
Lemma lem3759555 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759556 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759555 A P x). Qed.
Lemma lem3759557 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3759556 A s x). Qed.
Lemma lem3759558 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term485 A t x s) = (term486 A t s x).
Proof. exact (MK_COMB (@lem3759553 A t x) (@lem3759557 A s x)). Qed.
Lemma lem3759561 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term487 A t s) = (term488 A t s).
Proof. exact (fun_ext (fun x : A => @lem3759558 A t s x)). Qed.
Lemma lem3759562 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3759563 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term442 A t s) = (term489 A t s).
Proof. exact (MK_COMB (@lem3759562 A) (@lem3759561 A t s)). Qed.
Lemma lem3759568 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term445 A t s) = (term491 A t s).
Proof. exact (MK_COMB (@lem3759541 A s t) (@lem3759563 A t s)). Qed.
Lemma lem3759571 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term446 A f t s) = (term492 A f t s).
Proof. exact (MK_COMB (@lem3759511 A f t) (@lem3759568 A t s)). Qed.
Lemma lem3759574 {A : Type'} (f : type686 A) (s : A -> Prop) : (term447 A f s) = (term493 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3759571 A f t s)). Qed.
Lemma lem3759575 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3759576 {A : Type'} (f : type686 A) (s : A -> Prop) : (term448 A f s) = (term494 A f s).
Proof. exact (MK_COMB (@lem3759575 A) (@lem3759574 A f s)). Qed.
Lemma lem3759581 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3759582 {A : Type'} (f : type686 A) (s : A -> Prop) : (term459 A f s) = (term503 A f s).
Proof. exact (MK_COMB (@lem3759581) (@lem3759576 A f s)). Qed.
Lemma lem3759590 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759591 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3759590 (A -> Prop) P x). Qed.
Lemma lem3759592 {A : Type'} (f : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x f) = (f x).
Proof. exact (@lem3759591 A f x). Qed.
Lemma lem3759593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3759594 {A : Type'} (f : type686 A) (x : A -> Prop) : (term504 A x f) = (term505 A f x).
Proof. exact (MK_COMB (@lem3759593) (@lem3759592 A f x)). Qed.
Lemma lem3759596 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3759597 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x (@EMPTY (A -> Prop))) = False.
Proof. exact (@lem3759596 (A -> Prop) x). Qed.
Lemma lem3759598 {A : Type'} (f : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x f) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem3759594 A f x) (@lem3759597 A x)). Qed.
Lemma lem3759600 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3759601 {A : Type'} (f : type686 A) (x : A -> Prop) : ((f x) = False) = (term506 A f x).
Proof. exact (@lem3759600 (f x)). Qed.
Lemma lem3759602 {A : Type'} (f : type686 A) (x : A -> Prop) : ((@IN (A -> Prop) x f) = (@IN (A -> Prop) x (@EMPTY (A -> Prop)))) = (term506 A f x).
Proof. exact (TRANS (@lem3759598 A f x) (@lem3759601 A f x)). Qed.
Lemma lem3759603 {A : Type'} (f : type686 A) : (term507 A f) = (term508 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3759602 A f x)). Qed.
Lemma lem3759604 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3759605 {A : Type'} (f : type686 A) : (term467 A f) = (term509 A f).
Proof. exact (MK_COMB (@lem3759604 A) (@lem3759603 A f)). Qed.
Lemma lem3759610 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3759611 {A : Type'} (f : type686 A) : (term468 A f) = (term510 A f).
Proof. exact (MK_COMB (@lem3759610) (@lem3759605 A f)). Qed.
Lemma lem3759612 {A : Type'} (s : A -> Prop) (f : type686 A) : (term470 A s f) = (term511 A s f).
Proof. exact (MK_COMB (@lem3759582 A f s) (@lem3759611 A f)). Qed.
Lemma lem3759615 {A : Type'} (s : A -> Prop) (f : type686 A) : (term471 A s f) = (term512 A s f).
Proof. exact (MK_COMB (@lem3759497 A f s) (@lem3759612 A s f)). Qed.
Lemma lem3759618 {A : Type'} (s : A -> Prop) (f : type686 A) : (term472 A s f) = (term513 A s f).
Proof. exact (MK_COMB (@lem3759412 A f) (@lem3759615 A s f)). Qed.
Lemma lem3759621 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3759622 {A : Type'} (s : A -> Prop) (f : type686 A) : (term474 A s f) = (term514 A s f).
Proof. exact (MK_COMB (@lem3759621) (@lem3759618 A s f)). Qed.
Lemma lem3759632 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term515 A x s t) = (term516 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3759633 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term515 A x s t) = (term516 A s x t).
Proof. exact (@lem3759632 A s x t). Qed.
Lemma lem3759634 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) : (term517 A x s f) = (term518 A s x f).
Proof. exact (@lem3759633 A s x (@UNIONS A f)). Qed.
Lemma lem3759638 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759639 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759638 A P x). Qed.
Lemma lem3759640 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3759639 A s x). Qed.
Lemma lem3759641 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3759642 {A : Type'} (s : A -> Prop) (x : A) : (term519 A x s) = (term520 A s x).
Proof. exact (MK_COMB (@lem3759641) (@lem3759640 A s x)). Qed.
Lemma lem3759644 {A : Type'} (s : type686 A) (x : A) : (term521 A x s) = (term522 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3759645 {A : Type'} (s : type686 A) (x : A) : (term521 A x s) = (term522 A s x).
Proof. exact (@lem3759644 A s x). Qed.
Lemma lem3759646 {A : Type'} (f : type686 A) (x : A) : (term521 A x f) = (term522 A f x).
Proof. exact (@lem3759645 A f x). Qed.
Lemma lem3759654 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759655 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3759654 (A -> Prop) P x). Qed.
Lemma lem3759656 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3759655 A f t). Qed.
Lemma lem3759657 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3759658 {A : Type'} (f : type686 A) (t : A -> Prop) : (term523 A t f) = (term524 A f t).
Proof. exact (MK_COMB (@lem3759657) (@lem3759656 A f t)). Qed.
Lemma lem3759660 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759661 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759660 A P x). Qed.
Lemma lem3759662 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3759661 A t x). Qed.
Lemma lem3759663 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term525 A f x t) = (term526 A f t x).
Proof. exact (MK_COMB (@lem3759658 A f t) (@lem3759662 A t x)). Qed.
Lemma lem3759666 {A : Type'} (f : type686 A) (x : A) : (term527 A f x) = (term528 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3759663 A f t x)). Qed.
Lemma lem3759667 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3759668 {A : Type'} (f : type686 A) (x : A) : (term522 A f x) = (term529 A f x).
Proof. exact (MK_COMB (@lem3759667 A) (@lem3759666 A f x)). Qed.
Lemma lem3759673 {A : Type'} (f : type686 A) (x : A) : (term521 A x f) = (term529 A f x).
Proof. exact (TRANS (@lem3759646 A f x) (@lem3759668 A f x)). Qed.
Lemma lem3759674 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term518 A s x f) = (term530 A s f x).
Proof. exact (MK_COMB (@lem3759642 A s x) (@lem3759673 A f x)). Qed.
Lemma lem3759677 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term517 A x s f) = (term530 A s f x).
Proof. exact (TRANS (@lem3759634 A s x f) (@lem3759674 A s f x)). Qed.
Lemma lem3759678 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3759679 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term531 A x s f) = (term532 A s f x).
Proof. exact (MK_COMB (@lem3759678) (@lem3759677 A s f x)). Qed.
Lemma lem3759681 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759682 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759681 A P x). Qed.
Lemma lem3759683 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3759682 A s x). Qed.
Lemma lem3759684 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term517 A x s f) = (@IN A x s)) = ((term530 A s f x) = (s x)).
Proof. exact (MK_COMB (@lem3759679 A s f x) (@lem3759683 A s x)). Qed.
Lemma lem3759687 {A : Type'} (f : type686 A) (s : A -> Prop) : (term533 A f s) = (term534 A f s).
Proof. exact (fun_ext (fun x : A => @lem3759684 A f s x)). Qed.
Lemma lem3759688 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3759689 {A : Type'} (f : type686 A) (s : A -> Prop) : (term475 A f s) = (term535 A f s).
Proof. exact (MK_COMB (@lem3759688 A) (@lem3759687 A f s)). Qed.
Lemma lem3759694 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3759695 {A : Type'} (f : type686 A) (s : A -> Prop) : (term476 A f s) = (term536 A f s).
Proof. exact (MK_COMB (@lem3759694) (@lem3759689 A f s)). Qed.
Lemma lem3759703 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term515 A x s t) = (term516 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3759704 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term515 A x s t) = (term516 A s x t).
Proof. exact (@lem3759703 A s x t). Qed.
Lemma lem3759705 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) : (term517 A x s f) = (term518 A s x f).
Proof. exact (@lem3759704 A s x (@UNIONS A f)). Qed.
Lemma lem3759709 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759710 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759709 A P x). Qed.
Lemma lem3759711 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3759710 A s x). Qed.
Lemma lem3759712 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3759713 {A : Type'} (s : A -> Prop) (x : A) : (term519 A x s) = (term520 A s x).
Proof. exact (MK_COMB (@lem3759712) (@lem3759711 A s x)). Qed.
Lemma lem3759715 {A : Type'} (s : type686 A) (x : A) : (term521 A x s) = (term522 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3759716 {A : Type'} (s : type686 A) (x : A) : (term521 A x s) = (term522 A s x).
Proof. exact (@lem3759715 A s x). Qed.
Lemma lem3759717 {A : Type'} (f : type686 A) (x : A) : (term521 A x f) = (term522 A f x).
Proof. exact (@lem3759716 A f x). Qed.
Lemma lem3759725 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759726 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3759725 (A -> Prop) P x). Qed.
Lemma lem3759727 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3759726 A f t). Qed.
Lemma lem3759728 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3759729 {A : Type'} (f : type686 A) (t : A -> Prop) : (term523 A t f) = (term524 A f t).
Proof. exact (MK_COMB (@lem3759728) (@lem3759727 A f t)). Qed.
Lemma lem3759731 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759732 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759731 A P x). Qed.
Lemma lem3759733 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3759732 A t x). Qed.
Lemma lem3759734 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term525 A f x t) = (term526 A f t x).
Proof. exact (MK_COMB (@lem3759729 A f t) (@lem3759733 A t x)). Qed.
Lemma lem3759737 {A : Type'} (f : type686 A) (x : A) : (term527 A f x) = (term528 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3759734 A f t x)). Qed.
Lemma lem3759738 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3759739 {A : Type'} (f : type686 A) (x : A) : (term522 A f x) = (term529 A f x).
Proof. exact (MK_COMB (@lem3759738 A) (@lem3759737 A f x)). Qed.
Lemma lem3759744 {A : Type'} (f : type686 A) (x : A) : (term521 A x f) = (term529 A f x).
Proof. exact (TRANS (@lem3759717 A f x) (@lem3759739 A f x)). Qed.
Lemma lem3759745 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term518 A s x f) = (term530 A s f x).
Proof. exact (MK_COMB (@lem3759713 A s x) (@lem3759744 A f x)). Qed.
Lemma lem3759748 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term517 A x s f) = (term530 A s f x).
Proof. exact (TRANS (@lem3759705 A s x f) (@lem3759745 A s f x)). Qed.
Lemma lem3759749 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3759750 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term531 A x s f) = (term532 A s f x).
Proof. exact (MK_COMB (@lem3759749) (@lem3759748 A s f x)). Qed.
Lemma lem3759752 {A : Type'} (s : type686 A) (x : A) : (term521 A x s) = (term522 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3759753 {A : Type'} (s : type686 A) (x : A) : (term521 A x s) = (term522 A s x).
Proof. exact (@lem3759752 A s x). Qed.
Lemma lem3759754 {A : Type'} (f : type686 A) (x : A) : (term521 A x f) = (term522 A f x).
Proof. exact (@lem3759753 A f x). Qed.
Lemma lem3759762 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759763 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3759762 (A -> Prop) P x). Qed.
Lemma lem3759764 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3759763 A f t). Qed.
Lemma lem3759765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3759766 {A : Type'} (f : type686 A) (t : A -> Prop) : (term523 A t f) = (term524 A f t).
Proof. exact (MK_COMB (@lem3759765) (@lem3759764 A f t)). Qed.
Lemma lem3759768 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3759769 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3759768 A P x). Qed.
Lemma lem3759770 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3759769 A t x). Qed.
Lemma lem3759771 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term525 A f x t) = (term526 A f t x).
Proof. exact (MK_COMB (@lem3759766 A f t) (@lem3759770 A t x)). Qed.
Lemma lem3759774 {A : Type'} (f : type686 A) (x : A) : (term527 A f x) = (term528 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3759771 A f t x)). Qed.
Lemma lem3759775 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3759776 {A : Type'} (f : type686 A) (x : A) : (term522 A f x) = (term529 A f x).
Proof. exact (MK_COMB (@lem3759775 A) (@lem3759774 A f x)). Qed.
Lemma lem3759781 {A : Type'} (f : type686 A) (x : A) : (term521 A x f) = (term529 A f x).
Proof. exact (TRANS (@lem3759754 A f x) (@lem3759776 A f x)). Qed.
Lemma lem3759782 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term517 A x s f) = (term521 A x f)) = ((term530 A s f x) = (term529 A f x)).
Proof. exact (MK_COMB (@lem3759750 A s f x) (@lem3759781 A f x)). Qed.
Lemma lem3759785 {A : Type'} (s : A -> Prop) (f : type686 A) : (term537 A s f) = (term538 A s f).
Proof. exact (fun_ext (fun x : A => @lem3759782 A s f x)). Qed.
Lemma lem3759786 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3759787 {A : Type'} (s : A -> Prop) (f : type686 A) : (term477 A s f) = (term539 A s f).
Proof. exact (MK_COMB (@lem3759786 A) (@lem3759785 A s f)). Qed.
Lemma lem3759792 {A : Type'} (s : A -> Prop) (f : type686 A) : (term479 A s f) = (term540 A s f).
Proof. exact (MK_COMB (@lem3759695 A f s) (@lem3759787 A s f)). Qed.
Lemma lem3759795 {A : Type'} (s : A -> Prop) (f : type686 A) : (term481 A s f) = (term541 A s f).
Proof. exact (MK_COMB (@lem3759622 A s f) (@lem3759792 A s f)). Qed.
Lemma lem3759798 {A : Type'} (s : A -> Prop) (f : type686 A) : (term541 A s f) = (term481 A s f).
Proof. exact (SYM (@lem3759795 A s f)). Qed.
Lemma lem3759800 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3759801 {A : Type'} (s : A -> Prop) (f : type686 A) : (term541 A s f) = (term542 A s f).
Proof. exact (@lem3759800 (term541 A s f)). Qed.
Lemma lem3759802 {A : Type'} (s : A -> Prop) (f : type686 A) : (term542 A s f) = (term541 A s f).
Proof. exact (SYM (@lem3759801 A s f)). Qed.
Lemma lem3759803 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term543 A s f) : term543 A s f.
Proof. exact (h1). Qed.
Lemma lem3759806 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term542 A s f) : term542 A s f.
Proof. exact (h1). Qed.
Lemma lem3759807 {A : Type'} (s : A -> Prop) (f : type686 A) : term544 A s f.
Proof. exact (fun h0 : term542 A s f => @lem3759806 A s f h0). Qed.
Lemma lem3759808 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term544 A s f) : term544 A s f.
Proof. exact (h1). Qed.
Lemma lem3759809 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term542 A s f) : term542 A s f.
Proof. exact (h1). Qed.
Lemma lem3759810 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term542 A s f) (h2 : term544 A s f) : term542 A s f.
Proof. exact (@lem3759808 A s f h2 (@lem3759809 A s f h1)). Qed.
Lemma lem3759811 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term542 A s f) : term545 A s f.
Proof. exact (fun h0 : term544 A s f => @lem3759810 A s f h1 h0). Qed.
Lemma lem3759812 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term544 A s f) : term544 A s f.
Proof. exact (h1). Qed.
Lemma lem3759813 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term542 A s f) (h2 : term544 A s f) : term542 A s f.
Proof. exact (@lem3759811 A s f h1 (@lem3759812 A s f h2)). Qed.
Lemma lem3759814 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term544 A s f) : term544 A s f.
Proof. exact (fun h0 : term542 A s f => @lem3759813 A s f h0 h1). Qed.
Lemma lem3759815 {A : Type'} (s : A -> Prop) (f : type686 A) : term546 A s f.
Proof. exact (fun h0 : term544 A s f => @lem3759814 A s f h0). Qed.
Lemma lem3759818 {A : Type'} (s : A -> Prop) (f : type686 A) : term544 A s f.
Proof. exact (@lem3759815 A s f (@lem3759807 A s f)). Qed.
Lemma lem3759819 {A : Type'} (s : A -> Prop) (f : type686 A) : term544 A s f.
Proof. exact (@lem3759818 A s f). Qed.
Lemma lem3759829 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3759830 {A : Type'} (s : A -> Prop) (f : type686 A) : (term542 A s f) = (term547 A s f).
Proof. exact (@lem3759829 (term543 A s f)). Qed.
Lemma lem3759832 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3759833 {A : Type'} (s : A -> Prop) (f : type686 A) : (term547 A s f) = (term541 A s f).
Proof. exact (@lem3759832 (term541 A s f)). Qed.
Lemma lem3759836 {A : Type'} (s : A -> Prop) (f : type686 A) : (term542 A s f) = (term541 A s f).
Proof. exact (TRANS (@lem3759830 A s f) (@lem3759833 A s f)). Qed.
Lemma lem3760017 {A : Type'} (f : type686 A) : (term548 A f) = (term549 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3759836 A s f)). Qed.
Lemma lem3760018 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3760019 {A : Type'} (f : type686 A) : (term550 A f) = (term551 A f).
Proof. exact (MK_COMB (@lem3760018 A) (@lem3760017 A f)). Qed.
Lemma lem3760024 {A : Type'} : (term552 A) = (term553 A).
Proof. exact (fun_ext (fun f : type686 A => @lem3760019 A f)). Qed.
Lemma lem3760025 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3760034 {A : Type'} : (term554 A) = (term555 A).
Proof. exact (MK_COMB (@lem3760025 A) (@lem3760024 A)). Qed.
Lemma lem3760039 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term526 A f t x) = (term526 A f t x).
Proof. exact (eq_refl (term526 A f t x)). Qed.
Lemma lem3760040 {A : Type'} (f : type686 A) (x : A) : (term528 A f x) = (term528 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3760039 A f t x)). Qed.
Lemma lem3760041 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3760042 {A : Type'} (f : type686 A) (x : A) : (term529 A f x) = (term529 A f x).
Proof. exact (MK_COMB (@lem3760041 A) (@lem3760040 A f x)). Qed.
Lemma lem3760047 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term526 A f t x) = (term526 A f t x).
Proof. exact (eq_refl (term526 A f t x)). Qed.
Lemma lem3760048 {A : Type'} (f : type686 A) (x : A) : (term528 A f x) = (term528 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3760047 A f t x)). Qed.
Lemma lem3760049 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3760050 {A : Type'} (f : type686 A) (x : A) : (term529 A f x) = (term529 A f x).
Proof. exact (MK_COMB (@lem3760049 A) (@lem3760048 A f x)). Qed.
Lemma lem3760053 {A : Type'} (s : A -> Prop) (x : A) : (term520 A s x) = (term520 A s x).
Proof. exact (eq_refl (term520 A s x)). Qed.
Lemma lem3760054 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term530 A s f x) = (term530 A s f x).
Proof. exact (MK_COMB (@lem3760053 A s x) (@lem3760050 A f x)). Qed.
Lemma lem3760055 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3760056 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term532 A s f x) = (term532 A s f x).
Proof. exact (MK_COMB (@lem3760055) (@lem3760054 A s f x)). Qed.
Lemma lem3760057 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term530 A s f x) = (term529 A f x)) = ((term530 A s f x) = (term529 A f x)).
Proof. exact (MK_COMB (@lem3760056 A s f x) (@lem3760042 A f x)). Qed.
Lemma lem3760058 {A : Type'} (s : A -> Prop) (f : type686 A) : (term538 A s f) = (term538 A s f).
Proof. exact (fun_ext (fun x : A => @lem3760057 A s f x)). Qed.
Lemma lem3760059 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3760060 {A : Type'} (s : A -> Prop) (f : type686 A) : (term539 A s f) = (term539 A s f).
Proof. exact (MK_COMB (@lem3760059 A) (@lem3760058 A s f)). Qed.
Lemma lem3760061 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3760066 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term526 A f t x) = (term526 A f t x).
Proof. exact (eq_refl (term526 A f t x)). Qed.
Lemma lem3760067 {A : Type'} (f : type686 A) (x : A) : (term528 A f x) = (term528 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3760066 A f t x)). Qed.
Lemma lem3760068 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3760069 {A : Type'} (f : type686 A) (x : A) : (term529 A f x) = (term529 A f x).
Proof. exact (MK_COMB (@lem3760068 A) (@lem3760067 A f x)). Qed.
Lemma lem3760072 {A : Type'} (s : A -> Prop) (x : A) : (term520 A s x) = (term520 A s x).
Proof. exact (eq_refl (term520 A s x)). Qed.
Lemma lem3760073 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term530 A s f x) = (term530 A s f x).
Proof. exact (MK_COMB (@lem3760072 A s x) (@lem3760069 A f x)). Qed.
Lemma lem3760074 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3760075 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term532 A s f x) = (term532 A s f x).
Proof. exact (MK_COMB (@lem3760074) (@lem3760073 A s f x)). Qed.
Lemma lem3760076 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term530 A s f x) = (s x)) = ((term530 A s f x) = (s x)).
Proof. exact (MK_COMB (@lem3760075 A s f x) (@lem3760061 A s x)). Qed.
Lemma lem3760077 {A : Type'} (f : type686 A) (s : A -> Prop) : (term534 A f s) = (term534 A f s).
Proof. exact (fun_ext (fun x : A => @lem3760076 A f s x)). Qed.
Lemma lem3760078 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3760079 {A : Type'} (f : type686 A) (s : A -> Prop) : (term535 A f s) = (term535 A f s).
Proof. exact (MK_COMB (@lem3760078 A) (@lem3760077 A f s)). Qed.
Lemma lem3760080 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3760081 {A : Type'} (f : type686 A) (s : A -> Prop) : (term536 A f s) = (term536 A f s).
Proof. exact (MK_COMB (@lem3760080) (@lem3760079 A f s)). Qed.
Lemma lem3760082 {A : Type'} (s : A -> Prop) (f : type686 A) : (term540 A s f) = (term540 A s f).
Proof. exact (MK_COMB (@lem3760081 A f s) (@lem3760060 A s f)). Qed.
Lemma lem3760085 {A : Type'} (f : type686 A) (x : A -> Prop) : (term506 A f x) = (term506 A f x).
Proof. exact (eq_refl (term506 A f x)). Qed.
Lemma lem3760086 {A : Type'} (f : type686 A) : (term508 A f) = (term508 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3760085 A f x)). Qed.
Lemma lem3760087 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3760088 {A : Type'} (f : type686 A) : (term509 A f) = (term509 A f).
Proof. exact (MK_COMB (@lem3760087 A) (@lem3760086 A f)). Qed.
Lemma lem3760089 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3760090 {A : Type'} (f : type686 A) : (term510 A f) = (term510 A f).
Proof. exact (MK_COMB (@lem3760089) (@lem3760088 A f)). Qed.
Lemma lem3760095 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term486 A t s x) = (term486 A t s x).
Proof. exact (eq_refl (term486 A t s x)). Qed.
Lemma lem3760096 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term488 A t s) = (term488 A t s).
Proof. exact (fun_ext (fun x : A => @lem3760095 A t s x)). Qed.
Lemma lem3760097 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3760098 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term489 A t s) = (term489 A t s).
Proof. exact (MK_COMB (@lem3760097 A) (@lem3760096 A t s)). Qed.
Lemma lem3760103 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term486 A s t x) = (term486 A s t x).
Proof. exact (eq_refl (term486 A s t x)). Qed.
Lemma lem3760104 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term488 A s t) = (term488 A s t).
Proof. exact (fun_ext (fun x : A => @lem3760103 A s t x)). Qed.
Lemma lem3760105 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3760106 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term489 A s t) = (term489 A s t).
Proof. exact (MK_COMB (@lem3760105 A) (@lem3760104 A s t)). Qed.
Lemma lem3760107 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3760108 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term490 A s t) = (term490 A s t).
Proof. exact (MK_COMB (@lem3760107) (@lem3760106 A s t)). Qed.
Lemma lem3760109 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term491 A t s) = (term491 A t s).
Proof. exact (MK_COMB (@lem3760108 A s t) (@lem3760098 A t s)). Qed.
Lemma lem3760112 {A : Type'} (f : type686 A) (t : A -> Prop) : (term482 A f t) = (term482 A f t).
Proof. exact (eq_refl (term482 A f t)). Qed.
Lemma lem3760113 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term492 A f t s) = (term492 A f t s).
Proof. exact (MK_COMB (@lem3760112 A f t) (@lem3760109 A t s)). Qed.
Lemma lem3760114 {A : Type'} (f : type686 A) (s : A -> Prop) : (term493 A f s) = (term493 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3760113 A f t s)). Qed.
Lemma lem3760115 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3760116 {A : Type'} (f : type686 A) (s : A -> Prop) : (term494 A f s) = (term494 A f s).
Proof. exact (MK_COMB (@lem3760115 A) (@lem3760114 A f s)). Qed.
Lemma lem3760117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3760118 {A : Type'} (f : type686 A) (s : A -> Prop) : (term503 A f s) = (term503 A f s).
Proof. exact (MK_COMB (@lem3760117) (@lem3760116 A f s)). Qed.
Lemma lem3760119 {A : Type'} (s : A -> Prop) (f : type686 A) : (term511 A s f) = (term511 A s f).
Proof. exact (MK_COMB (@lem3760118 A f s) (@lem3760090 A f)). Qed.
Lemma lem3760124 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term486 A s s' x) = (term486 A s s' x).
Proof. exact (eq_refl (term486 A s s' x)). Qed.
Lemma lem3760125 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term488 A s s') = (term488 A s s').
Proof. exact (fun_ext (fun x : A => @lem3760124 A s s' x)). Qed.
Lemma lem3760126 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3760127 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term489 A s s') = (term489 A s s').
Proof. exact (MK_COMB (@lem3760126 A) (@lem3760125 A s s')). Qed.
Lemma lem3760132 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term486 A s' s x) = (term486 A s' s x).
Proof. exact (eq_refl (term486 A s' s x)). Qed.
Lemma lem3760133 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term488 A s' s) = (term488 A s' s).
Proof. exact (fun_ext (fun x : A => @lem3760132 A s' s x)). Qed.
Lemma lem3760134 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3760135 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term489 A s' s) = (term489 A s' s).
Proof. exact (MK_COMB (@lem3760134 A) (@lem3760133 A s' s)). Qed.
Lemma lem3760136 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3760137 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term490 A s' s) = (term490 A s' s).
Proof. exact (MK_COMB (@lem3760136) (@lem3760135 A s' s)). Qed.
Lemma lem3760138 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term491 A s s') = (term491 A s s').
Proof. exact (MK_COMB (@lem3760137 A s' s) (@lem3760127 A s s')). Qed.
Lemma lem3760141 {A : Type'} (f : type686 A) (s' : A -> Prop) : (term482 A f s') = (term482 A f s').
Proof. exact (eq_refl (term482 A f s')). Qed.
Lemma lem3760142 {A : Type'} (f : type686 A) (s : A -> Prop) (s' : A -> Prop) : (term499 A f s s') = (term499 A f s s').
Proof. exact (MK_COMB (@lem3760141 A f s') (@lem3760138 A s s')). Qed.
Lemma lem3760143 {A : Type'} (f : type686 A) (s : A -> Prop) : (term500 A f s) = (term500 A f s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3760142 A f s s')). Qed.
Lemma lem3760144 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3760145 {A : Type'} (f : type686 A) (s : A -> Prop) : (term501 A f s) = (term501 A f s).
Proof. exact (MK_COMB (@lem3760144 A) (@lem3760143 A f s)). Qed.
Lemma lem3760146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3760147 {A : Type'} (f : type686 A) (s : A -> Prop) : (term502 A f s) = (term502 A f s).
Proof. exact (MK_COMB (@lem3760146) (@lem3760145 A f s)). Qed.
Lemma lem3760148 {A : Type'} (s : A -> Prop) (f : type686 A) : (term512 A s f) = (term512 A s f).
Proof. exact (MK_COMB (@lem3760147 A f s) (@lem3760119 A s f)). Qed.
Lemma lem3760153 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term486 A t s x) = (term486 A t s x).
Proof. exact (eq_refl (term486 A t s x)). Qed.
Lemma lem3760154 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term488 A t s) = (term488 A t s).
Proof. exact (fun_ext (fun x : A => @lem3760153 A t s x)). Qed.
Lemma lem3760155 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3760156 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term489 A t s) = (term489 A t s).
Proof. exact (MK_COMB (@lem3760155 A) (@lem3760154 A t s)). Qed.
Lemma lem3760161 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term486 A s t x) = (term486 A s t x).
Proof. exact (eq_refl (term486 A s t x)). Qed.
Lemma lem3760162 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term488 A s t) = (term488 A s t).
Proof. exact (fun_ext (fun x : A => @lem3760161 A s t x)). Qed.
Lemma lem3760163 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3760164 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term489 A s t) = (term489 A s t).
Proof. exact (MK_COMB (@lem3760163 A) (@lem3760162 A s t)). Qed.
Lemma lem3760165 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3760166 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term490 A s t) = (term490 A s t).
Proof. exact (MK_COMB (@lem3760165) (@lem3760164 A s t)). Qed.
Lemma lem3760167 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term491 A t s) = (term491 A t s).
Proof. exact (MK_COMB (@lem3760166 A s t) (@lem3760156 A t s)). Qed.
Lemma lem3760170 {A : Type'} (f : type686 A) (t : A -> Prop) : (term482 A f t) = (term482 A f t).
Proof. exact (eq_refl (term482 A f t)). Qed.
Lemma lem3760171 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term492 A f t s) = (term492 A f t s).
Proof. exact (MK_COMB (@lem3760170 A f t) (@lem3760167 A t s)). Qed.
Lemma lem3760172 {A : Type'} (f : type686 A) (s : A -> Prop) : (term493 A f s) = (term493 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3760171 A f t s)). Qed.
Lemma lem3760173 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3760174 {A : Type'} (f : type686 A) (s : A -> Prop) : (term494 A f s) = (term494 A f s).
Proof. exact (MK_COMB (@lem3760173 A) (@lem3760172 A f s)). Qed.
Lemma lem3760177 {A : Type'} (f : type686 A) (s : A -> Prop) : (term482 A f s) = (term482 A f s).
Proof. exact (eq_refl (term482 A f s)). Qed.
Lemma lem3760178 {A : Type'} (f : type686 A) (s : A -> Prop) : (term495 A f s) = (term495 A f s).
Proof. exact (MK_COMB (@lem3760177 A f s) (@lem3760174 A f s)). Qed.
Lemma lem3760179 {A : Type'} (f : type686 A) : (term496 A f) = (term496 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3760178 A f s)). Qed.
Lemma lem3760180 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3760181 {A : Type'} (f : type686 A) : (term497 A f) = (term497 A f).
Proof. exact (MK_COMB (@lem3760180 A) (@lem3760179 A f)). Qed.
Lemma lem3760182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3760183 {A : Type'} (f : type686 A) : (term498 A f) = (term498 A f).
Proof. exact (MK_COMB (@lem3760182) (@lem3760181 A f)). Qed.
Lemma lem3760184 {A : Type'} (s : A -> Prop) (f : type686 A) : (term513 A s f) = (term513 A s f).
Proof. exact (MK_COMB (@lem3760183 A f) (@lem3760148 A s f)). Qed.
Lemma lem3760185 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3760186 {A : Type'} (s : A -> Prop) (f : type686 A) : (term514 A s f) = (term514 A s f).
Proof. exact (MK_COMB (@lem3760185) (@lem3760184 A s f)). Qed.
Lemma lem3760187 {A : Type'} (s : A -> Prop) (f : type686 A) : (term541 A s f) = (term541 A s f).
Proof. exact (MK_COMB (@lem3760186 A s f) (@lem3760082 A s f)). Qed.
Lemma lem3760188 {A : Type'} (f : type686 A) : (term549 A f) = (term549 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3760187 A s f)). Qed.
Lemma lem3760189 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3760190 {A : Type'} (f : type686 A) : (term551 A f) = (term551 A f).
Proof. exact (MK_COMB (@lem3760189 A) (@lem3760188 A f)). Qed.
Lemma lem3760191 {A : Type'} : (term553 A) = (term553 A).
Proof. exact (fun_ext (fun f : type686 A => @lem3760190 A f)). Qed.
Lemma lem3760192 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3760193 {A : Type'} : (term555 A) = (term555 A).
Proof. exact (MK_COMB (@lem3760192 A) (@lem3760191 A)). Qed.
Lemma lem3760350 {A : Type'} : (term554 A) = (term555 A).
Proof. exact (TRANS (@lem3760034 A) (@lem3760193 A)). Qed.
Lemma lem3760351 {A : Type'} : (term555 A) = (term554 A).
Proof. exact (SYM (@lem3760350 A)). Qed.
Lemma lem3760352 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term513 A s f) : term513 A s f.
Proof. exact (h1). Qed.
Lemma lem3760354 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3760355 {A : Type'} (s : A -> Prop) (f : type686 A) : (term540 A s f) = (term556 A s f).
Proof. exact (@lem3760354 (term540 A s f)). Qed.
Lemma lem3760356 {A : Type'} (s : A -> Prop) (f : type686 A) : (term556 A s f) = (term540 A s f).
Proof. exact (SYM (@lem3760355 A s f)). Qed.
Lemma lem3760357 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term557 A s f) : term557 A s f.
Proof. exact (h1). Qed.
Lemma lem3760366 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term486 A s t x) = (term558 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3760367 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term488 A s t) = (term559 A s t).
Proof. exact (fun_ext (fun x : A => @lem3760366 A s t x)). Qed.
Lemma lem3760368 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3760369 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term489 A s t) = (term560 A s t).
Proof. exact (MK_COMB (@lem3760368 A) (@lem3760367 A s t)). Qed.
Lemma lem3760376 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term486 A t s x) = (term558 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem3760377 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term488 A t s) = (term559 A t s).
Proof. exact (fun_ext (fun x : A => @lem3760376 A t s x)). Qed.
Lemma lem3760378 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3760379 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term489 A t s) = (term560 A t s).
Proof. exact (MK_COMB (@lem3760378 A) (@lem3760377 A t s)). Qed.
Lemma lem3760380 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3760381 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term490 A s t) = (term561 A s t).
Proof. exact (MK_COMB (@lem3760380) (@lem3760369 A s t)). Qed.
Lemma lem3760382 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term491 A t s) = (term562 A t s).
Proof. exact (MK_COMB (@lem3760381 A s t) (@lem3760379 A t s)). Qed.
Lemma lem3760384 {A : Type'} (f : type686 A) (t : A -> Prop) : (term563 A f t) = (term563 A f t).
Proof. exact (eq_refl (term563 A f t)). Qed.
Lemma lem3760385 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term564 A f t s) = (term565 A f t s).
Proof. exact (MK_COMB (@lem3760384 A f t) (@lem3760382 A t s)). Qed.
Lemma lem3760386 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term492 A f t s) = (term564 A f t s).
Proof. exact (@lem17265 (f t) (term491 A t s)). Qed.
Lemma lem3760387 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term492 A f t s) = (term565 A f t s).
Proof. exact (TRANS (@lem3760386 A f t s) (@lem3760385 A f t s)). Qed.
Lemma lem3760388 {A : Type'} (f : type686 A) (s : A -> Prop) : (term493 A f s) = (term566 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3760387 A f t s)). Qed.
Lemma lem3760389 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3760390 {A : Type'} (f : type686 A) (s : A -> Prop) : (term494 A f s) = (term567 A f s).
Proof. exact (MK_COMB (@lem3760389 A) (@lem3760388 A f s)). Qed.
Lemma lem3760392 {A : Type'} (f : type686 A) (s : A -> Prop) : (term563 A f s) = (term563 A f s).
Proof. exact (eq_refl (term563 A f s)). Qed.
Lemma lem3760393 {A : Type'} (f : type686 A) (s : A -> Prop) : (term568 A f s) = (term569 A f s).
Proof. exact (MK_COMB (@lem3760392 A f s) (@lem3760390 A f s)). Qed.
Lemma lem3760394 {A : Type'} (f : type686 A) (s : A -> Prop) : (term495 A f s) = (term568 A f s).
Proof. exact (@lem17265 (f s) (term494 A f s)). Qed.
Lemma lem3760395 {A : Type'} (f : type686 A) (s : A -> Prop) : (term495 A f s) = (term569 A f s).
Proof. exact (TRANS (@lem3760394 A f s) (@lem3760393 A f s)). Qed.
Lemma lem3760396 {A : Type'} (f : type686 A) : (term496 A f) = (term570 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3760395 A f s)). Qed.
Lemma lem3760397 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3760398 {A : Type'} (f : type686 A) : (term497 A f) = (term571 A f).
Proof. exact (MK_COMB (@lem3760397 A) (@lem3760396 A f)). Qed.
Lemma lem3760406 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term486 A s' s x) = (term558 A s' s x).
Proof. exact (@lem17265 (s' x) (s x)). Qed.
Lemma lem3760407 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term488 A s' s) = (term559 A s' s).
Proof. exact (fun_ext (fun x : A => @lem3760406 A s' s x)). Qed.
Lemma lem3760408 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3760409 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term489 A s' s) = (term560 A s' s).
Proof. exact (MK_COMB (@lem3760408 A) (@lem3760407 A s' s)). Qed.
Lemma lem3760416 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term486 A s s' x) = (term558 A s s' x).
Proof. exact (@lem17265 (s x) (s' x)). Qed.
Lemma lem3760417 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term488 A s s') = (term559 A s s').
Proof. exact (fun_ext (fun x : A => @lem3760416 A s s' x)). Qed.
Lemma lem3760418 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3760419 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term489 A s s') = (term560 A s s').
Proof. exact (MK_COMB (@lem3760418 A) (@lem3760417 A s s')). Qed.
Lemma lem3760420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3760421 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term490 A s' s) = (term561 A s' s).
Proof. exact (MK_COMB (@lem3760420) (@lem3760409 A s' s)). Qed.
Lemma lem3760422 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term491 A s s') = (term562 A s s').
Proof. exact (MK_COMB (@lem3760421 A s' s) (@lem3760419 A s s')). Qed.
Lemma lem3760424 {A : Type'} (f : type686 A) (s' : A -> Prop) : (term563 A f s') = (term563 A f s').
Proof. exact (eq_refl (term563 A f s')). Qed.
Lemma lem3760425 {A : Type'} (f : type686 A) (s : A -> Prop) (s' : A -> Prop) : (term572 A f s s') = (term573 A f s s').
Proof. exact (MK_COMB (@lem3760424 A f s') (@lem3760422 A s s')). Qed.
Lemma lem3760426 {A : Type'} (f : type686 A) (s : A -> Prop) (s' : A -> Prop) : (term499 A f s s') = (term572 A f s s').
Proof. exact (@lem17265 (f s') (term491 A s s')). Qed.
Lemma lem3760427 {A : Type'} (f : type686 A) (s : A -> Prop) (s' : A -> Prop) : (term499 A f s s') = (term573 A f s s').
Proof. exact (TRANS (@lem3760426 A f s s') (@lem3760425 A f s s')). Qed.
Lemma lem3760428 {A : Type'} (f : type686 A) (s : A -> Prop) : (term500 A f s) = (term574 A f s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3760427 A f s s')). Qed.
Lemma lem3760429 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3760430 {A : Type'} (f : type686 A) (s : A -> Prop) : (term501 A f s) = (term575 A f s).
Proof. exact (MK_COMB (@lem3760429 A) (@lem3760428 A f s)). Qed.
Lemma lem3760438 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term486 A s t x) = (term558 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3760439 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term488 A s t) = (term559 A s t).
Proof. exact (fun_ext (fun x : A => @lem3760438 A s t x)). Qed.
Lemma lem3760440 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3760441 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term489 A s t) = (term560 A s t).
Proof. exact (MK_COMB (@lem3760440 A) (@lem3760439 A s t)). Qed.
Lemma lem3760448 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term486 A t s x) = (term558 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem3760449 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term488 A t s) = (term559 A t s).
Proof. exact (fun_ext (fun x : A => @lem3760448 A t s x)). Qed.
Lemma lem3760450 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3760451 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term489 A t s) = (term560 A t s).
Proof. exact (MK_COMB (@lem3760450 A) (@lem3760449 A t s)). Qed.
Lemma lem3760452 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3760453 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term490 A s t) = (term561 A s t).
Proof. exact (MK_COMB (@lem3760452) (@lem3760441 A s t)). Qed.
Lemma lem3760454 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term491 A t s) = (term562 A t s).
Proof. exact (MK_COMB (@lem3760453 A s t) (@lem3760451 A t s)). Qed.
Lemma lem3760456 {A : Type'} (f : type686 A) (t : A -> Prop) : (term563 A f t) = (term563 A f t).
Proof. exact (eq_refl (term563 A f t)). Qed.
Lemma lem3760457 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term564 A f t s) = (term565 A f t s).
Proof. exact (MK_COMB (@lem3760456 A f t) (@lem3760454 A t s)). Qed.
Lemma lem3760458 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term492 A f t s) = (term564 A f t s).
Proof. exact (@lem17265 (f t) (term491 A t s)). Qed.
Lemma lem3760459 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term492 A f t s) = (term565 A f t s).
Proof. exact (TRANS (@lem3760458 A f t s) (@lem3760457 A f t s)). Qed.
Lemma lem3760460 {A : Type'} (f : type686 A) (s : A -> Prop) : (term493 A f s) = (term566 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3760459 A f t s)). Qed.
Lemma lem3760461 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3760462 {A : Type'} (f : type686 A) (s : A -> Prop) : (term494 A f s) = (term567 A f s).
Proof. exact (MK_COMB (@lem3760461 A) (@lem3760460 A f s)). Qed.
Lemma lem3760465 {A : Type'} (f : type686 A) (x : A -> Prop) : (term576 A f x) = (f x).
Proof. exact (@lem16933 (f x)). Qed.
Lemma lem3760466 {A : Type'} (P : type686 A) : (term577 A P) = (term578 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3760467 {A : Type'} (f : type686 A) : (term510 A f) = (term579 A f).
Proof. exact (@lem3760466 A (term508 A f)). Qed.
Lemma lem3760468 {A : Type'} (f : type686 A) (x : A -> Prop) : (term580 A f x) = (term506 A f x).
Proof. exact (eq_refl (term580 A f x)). Qed.
Lemma lem3760469 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3760470 {A : Type'} (f : type686 A) (x : A -> Prop) : (term581 A f x) = (term576 A f x).
Proof. exact (MK_COMB (@lem3760469) (@lem3760468 A f x)). Qed.
Lemma lem3760471 {A : Type'} (f : type686 A) (x : A -> Prop) : (term581 A f x) = (f x).
Proof. exact (TRANS (@lem3760470 A f x) (@lem3760465 A f x)). Qed.
Lemma lem3760472 {A : Type'} (f : type686 A) : (term582 A f) = (term583 A f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3760471 A f x)). Qed.
Lemma lem3760473 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3760474 {A : Type'} (f : type686 A) : (term579 A f) = (term584 A f).
Proof. exact (MK_COMB (@lem3760473 A) (@lem3760472 A f)). Qed.
Lemma lem3760475 {A : Type'} (f : type686 A) : (term510 A f) = (term584 A f).
Proof. exact (TRANS (@lem3760467 A f) (@lem3760474 A f)). Qed.
Lemma lem3760476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3760477 {A : Type'} (f : type686 A) (s : A -> Prop) : (term503 A f s) = (term585 A f s).
Proof. exact (MK_COMB (@lem3760476) (@lem3760462 A f s)). Qed.
Lemma lem3760478 {A : Type'} (s : A -> Prop) (f : type686 A) : (term511 A s f) = (term586 A s f).
Proof. exact (MK_COMB (@lem3760477 A f s) (@lem3760475 A f)). Qed.
Lemma lem3760479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3760480 {A : Type'} (f : type686 A) (s : A -> Prop) : (term502 A f s) = (term587 A f s).
Proof. exact (MK_COMB (@lem3760479) (@lem3760430 A f s)). Qed.
Lemma lem3760481 {A : Type'} (s : A -> Prop) (f : type686 A) : (term512 A s f) = (term588 A s f).
Proof. exact (MK_COMB (@lem3760480 A f s) (@lem3760478 A s f)). Qed.
Lemma lem3760482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3760483 {A : Type'} (f : type686 A) : (term498 A f) = (term589 A f).
Proof. exact (MK_COMB (@lem3760482) (@lem3760398 A f)). Qed.
Lemma lem3760484 {A : Type'} (s : A -> Prop) (f : type686 A) : (term513 A s f) = (term590 A s f).
Proof. exact (MK_COMB (@lem3760483 A f) (@lem3760481 A s f)). Qed.
Lemma lem3760875 {A : Type'} (P : Prop) (Q : A -> Prop) : (term591 A P Q) = (term592 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3760876 {A : Type'} (P : Prop) (Q : type686 A) : (term593 A P Q) = (term594 A P Q).
Proof. exact (@lem3760875 (A -> Prop) P Q). Qed.
Lemma lem3760877 {A : Type'} (s : A -> Prop) (f : type686 A) : (term586 A s f) = (term595 A s f).
Proof. exact (@lem3760876 A (term567 A f s) f). Qed.
Lemma lem3760878 {A : Type'} (f : type686 A) (s : A -> Prop) : (term587 A f s) = (term587 A f s).
Proof. exact (eq_refl (term587 A f s)). Qed.
Lemma lem3760879 {A : Type'} (s : A -> Prop) (f : type686 A) : (term588 A s f) = (term596 A s f).
Proof. exact (MK_COMB (@lem3760878 A f s) (@lem3760877 A s f)). Qed.
Lemma lem3760881 {A : Type'} (P : Prop) (Q : A -> Prop) : (term591 A P Q) = (term592 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3760882 {A : Type'} (P : Prop) (Q : type686 A) : (term593 A P Q) = (term594 A P Q).
Proof. exact (@lem3760881 (A -> Prop) P Q). Qed.
Lemma lem3760883 {A : Type'} (s : A -> Prop) (f : type686 A) : (term597 A s f) = (term598 A s f).
Proof. exact (@lem3760882 A (term575 A f s) (term599 A s f)). Qed.
Lemma lem3760884 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term600 A s f x) = (term601 A s f x).
Proof. exact (eq_refl (term600 A s f x)). Qed.
Lemma lem3760885 {A : Type'} (s : A -> Prop) (f : type686 A) : (term602 A s f) = (term599 A s f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3760884 A s f x)). Qed.
Lemma lem3760886 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3760887 {A : Type'} (s : A -> Prop) (f : type686 A) : (term603 A s f) = (term595 A s f).
Proof. exact (MK_COMB (@lem3760886 A) (@lem3760885 A s f)). Qed.
Lemma lem3760888 {A : Type'} (f : type686 A) (s : A -> Prop) : (term587 A f s) = (term587 A f s).
Proof. exact (eq_refl (term587 A f s)). Qed.
Lemma lem3760889 {A : Type'} (s : A -> Prop) (f : type686 A) : (term597 A s f) = (term596 A s f).
Proof. exact (MK_COMB (@lem3760888 A f s) (@lem3760887 A s f)). Qed.
Lemma lem3760890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3760891 {A : Type'} (s : A -> Prop) (f : type686 A) : (term604 A s f) = (term605 A s f).
Proof. exact (MK_COMB (@lem3760890) (@lem3760889 A s f)). Qed.
Lemma lem3760892 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term600 A s f x) = (term601 A s f x).
Proof. exact (eq_refl (term600 A s f x)). Qed.
Lemma lem3760893 {A : Type'} (f : type686 A) (s : A -> Prop) : (term587 A f s) = (term587 A f s).
Proof. exact (eq_refl (term587 A f s)). Qed.
Lemma lem3760894 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term606 A s f x) = (term607 A s f x).
Proof. exact (MK_COMB (@lem3760893 A f s) (@lem3760892 A s f x)). Qed.
Lemma lem3760895 {A : Type'} (s : A -> Prop) (f : type686 A) : (term608 A s f) = (term609 A s f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3760894 A s f x)). Qed.
Lemma lem3760896 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3760897 {A : Type'} (s : A -> Prop) (f : type686 A) : (term598 A s f) = (term610 A s f).
Proof. exact (MK_COMB (@lem3760896 A) (@lem3760895 A s f)). Qed.
Lemma lem3760898 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term597 A s f) = (term598 A s f)) = ((term596 A s f) = (term610 A s f)).
Proof. exact (MK_COMB (@lem3760891 A s f) (@lem3760897 A s f)). Qed.
Lemma lem3760899 {A : Type'} (s : A -> Prop) (f : type686 A) : (term596 A s f) = (term610 A s f).
Proof. exact (EQ_MP (@lem3760898 A s f) (@lem3760883 A s f)). Qed.
Lemma lem3760900 {A : Type'} (s : A -> Prop) (f : type686 A) : (term588 A s f) = (term610 A s f).
Proof. exact (TRANS (@lem3760879 A s f) (@lem3760899 A s f)). Qed.
Lemma lem3760901 {A : Type'} (f : type686 A) : (term589 A f) = (term589 A f).
Proof. exact (eq_refl (term589 A f)). Qed.
Lemma lem3760902 {A : Type'} (s : A -> Prop) (f : type686 A) : (term590 A s f) = (term611 A s f).
Proof. exact (MK_COMB (@lem3760901 A f) (@lem3760900 A s f)). Qed.
Lemma lem3760904 {A : Type'} (P : Prop) (Q : A -> Prop) : (term591 A P Q) = (term592 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3760905 {A : Type'} (P : Prop) (Q : type686 A) : (term593 A P Q) = (term594 A P Q).
Proof. exact (@lem3760904 (A -> Prop) P Q). Qed.
Lemma lem3760906 {A : Type'} (s : A -> Prop) (f : type686 A) : (term612 A s f) = (term613 A s f).
Proof. exact (@lem3760905 A (term571 A f) (term609 A s f)). Qed.
Lemma lem3760907 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term614 A s f x) = (term607 A s f x).
Proof. exact (eq_refl (term614 A s f x)). Qed.
Lemma lem3760908 {A : Type'} (s : A -> Prop) (f : type686 A) : (term615 A s f) = (term609 A s f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3760907 A s f x)). Qed.
Lemma lem3760909 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3760910 {A : Type'} (s : A -> Prop) (f : type686 A) : (term616 A s f) = (term610 A s f).
Proof. exact (MK_COMB (@lem3760909 A) (@lem3760908 A s f)). Qed.
Lemma lem3760911 {A : Type'} (f : type686 A) : (term589 A f) = (term589 A f).
Proof. exact (eq_refl (term589 A f)). Qed.
Lemma lem3760912 {A : Type'} (s : A -> Prop) (f : type686 A) : (term612 A s f) = (term611 A s f).
Proof. exact (MK_COMB (@lem3760911 A f) (@lem3760910 A s f)). Qed.
Lemma lem3760913 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3760914 {A : Type'} (s : A -> Prop) (f : type686 A) : (term617 A s f) = (term618 A s f).
Proof. exact (MK_COMB (@lem3760913) (@lem3760912 A s f)). Qed.
Lemma lem3760915 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term614 A s f x) = (term607 A s f x).
Proof. exact (eq_refl (term614 A s f x)). Qed.
Lemma lem3760916 {A : Type'} (f : type686 A) : (term589 A f) = (term589 A f).
Proof. exact (eq_refl (term589 A f)). Qed.
Lemma lem3760917 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A -> Prop) : (term619 A s f x) = (term620 A s f x).
Proof. exact (MK_COMB (@lem3760916 A f) (@lem3760915 A s f x)). Qed.
Lemma lem3760918 {A : Type'} (s : A -> Prop) (f : type686 A) : (term621 A s f) = (term622 A s f).
Proof. exact (fun_ext (fun x : A -> Prop => @lem3760917 A s f x)). Qed.
Lemma lem3760919 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3760920 {A : Type'} (s : A -> Prop) (f : type686 A) : (term613 A s f) = (term623 A s f).
Proof. exact (MK_COMB (@lem3760919 A) (@lem3760918 A s f)). Qed.
Lemma lem3760921 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term612 A s f) = (term613 A s f)) = ((term611 A s f) = (term623 A s f)).
Proof. exact (MK_COMB (@lem3760914 A s f) (@lem3760920 A s f)). Qed.
Lemma lem3760922 {A : Type'} (s : A -> Prop) (f : type686 A) : (term611 A s f) = (term623 A s f).
Proof. exact (EQ_MP (@lem3760921 A s f) (@lem3760906 A s f)). Qed.
Lemma lem3760924 {A : Type'} (s : A -> Prop) (f : type686 A) : (term590 A s f) = (term623 A s f).
Proof. exact (TRANS (@lem3760902 A s f) (@lem3760922 A s f)). Qed.
Lemma lem3760925 {A : Type'} (s : A -> Prop) (f : type686 A) : (term513 A s f) = (term623 A s f).
Proof. exact (TRANS (@lem3760484 A s f) (@lem3760924 A s f)). Qed.
Lemma lem3760926 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term513 A s f) : term623 A s f.
Proof. exact (EQ_MP (@lem3760925 A s f) (@lem3760352 A s f h1)). Qed.
Lemma lem3760937 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term624 A f t x) = (term625 A f t x).
Proof. exact (@lem17045 (f t) (t x)). Qed.
Lemma lem3760940 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term526 A f t x) = (term526 A f t x).
Proof. exact (eq_refl (term526 A f t x)). Qed.
Lemma lem3760941 {A : Type'} (P : type686 A) : (term626 A P) = (term509 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3760942 {A : Type'} (f : type686 A) (x : A) : (term627 A f x) = (term628 A f x).
Proof. exact (@lem3760941 A (term528 A f x)). Qed.
Lemma lem3760943 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term629 A f x t) = (term526 A f t x).
Proof. exact (eq_refl (term629 A f x t)). Qed.
Lemma lem3760944 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3760945 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term630 A f x t) = (term624 A f t x).
Proof. exact (MK_COMB (@lem3760944) (@lem3760943 A f t x)). Qed.
Lemma lem3760946 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term630 A f x t) = (term625 A f t x).
Proof. exact (TRANS (@lem3760945 A f t x) (@lem3760937 A f t x)). Qed.
Lemma lem3760947 {A : Type'} (f : type686 A) (x : A) : (term631 A f x) = (term632 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3760946 A f t x)). Qed.
Lemma lem3760948 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3760949 {A : Type'} (f : type686 A) (x : A) : (term628 A f x) = (term633 A f x).
Proof. exact (MK_COMB (@lem3760948 A) (@lem3760947 A f x)). Qed.
Lemma lem3760950 {A : Type'} (f : type686 A) (x : A) : (term627 A f x) = (term633 A f x).
Proof. exact (TRANS (@lem3760942 A f x) (@lem3760949 A f x)). Qed.
Lemma lem3760951 {A : Type'} (f : type686 A) (x : A) : (term528 A f x) = (term528 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3760940 A f t x)). Qed.
Lemma lem3760952 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3760953 {A : Type'} (f : type686 A) (x : A) : (term529 A f x) = (term529 A f x).
Proof. exact (MK_COMB (@lem3760952 A) (@lem3760951 A f x)). Qed.
Lemma lem3760955 {A : Type'} (s : A -> Prop) (x : A) : (term634 A s x) = (term634 A s x).
Proof. exact (eq_refl (term634 A s x)). Qed.
Lemma lem3760956 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term635 A s f x) = (term636 A s f x).
Proof. exact (MK_COMB (@lem3760955 A s x) (@lem3760950 A f x)). Qed.
Lemma lem3760957 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term637 A s f x) = (term635 A s f x).
Proof. exact (@lem17160 (s x) (term529 A f x)). Qed.
Lemma lem3760958 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term637 A s f x) = (term636 A s f x).
Proof. exact (TRANS (@lem3760957 A s f x) (@lem3760956 A s f x)). Qed.
Lemma lem3760960 {A : Type'} (s : A -> Prop) (x : A) : (term520 A s x) = (term520 A s x).
Proof. exact (eq_refl (term520 A s x)). Qed.
Lemma lem3760961 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term530 A s f x) = (term530 A s f x).
Proof. exact (MK_COMB (@lem3760960 A s x) (@lem3760953 A f x)). Qed.
Lemma lem3760962 {A : Type'} (s : A -> Prop) (x : A) : (term638 A s x) = (term638 A s x).
Proof. exact (eq_refl (term638 A s x)). Qed.
Lemma lem3760963 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3760964 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3760965 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term639 A s f x) = (term640 A s f x).
Proof. exact (MK_COMB (@lem3760964) (@lem3760958 A s f x)). Qed.
Lemma lem3760966 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term641 A f s x) = (term642 A f s x).
Proof. exact (MK_COMB (@lem3760965 A s f x) (@lem3760963 A s x)). Qed.
Lemma lem3760967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3760968 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term643 A s f x) = (term643 A s f x).
Proof. exact (MK_COMB (@lem3760967) (@lem3760961 A s f x)). Qed.
Lemma lem3760969 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term644 A f s x) = (term644 A f s x).
Proof. exact (MK_COMB (@lem3760968 A s f x) (@lem3760962 A s x)). Qed.
Lemma lem3760970 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3760971 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term645 A f s x) = (term645 A f s x).
Proof. exact (MK_COMB (@lem3760970) (@lem3760969 A f s x)). Qed.
Lemma lem3760972 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term646 A f s x) = (term647 A f s x).
Proof. exact (MK_COMB (@lem3760971 A f s x) (@lem3760966 A f s x)). Qed.
Lemma lem3760973 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term648 A f s x) = (term646 A f s x).
Proof. exact (@lem17646 (term530 A s f x) (s x)). Qed.
Lemma lem3760974 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term648 A f s x) = (term647 A f s x).
Proof. exact (TRANS (@lem3760973 A f s x) (@lem3760972 A f s x)). Qed.
Lemma lem3760975 {A : Type'} (P : A -> Prop) : (term649 A P) = (term650 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3760976 {A : Type'} (f : type686 A) (s : A -> Prop) : (term651 A f s) = (term652 A f s).
Proof. exact (@lem3760975 A (term534 A f s)). Qed.
Lemma lem3760977 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term653 A f s x) = ((term530 A s f x) = (s x)).
Proof. exact (eq_refl (term653 A f s x)). Qed.
Lemma lem3760978 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3760979 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term654 A f s x) = (term648 A f s x).
Proof. exact (MK_COMB (@lem3760978) (@lem3760977 A f s x)). Qed.
Lemma lem3760980 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term654 A f s x) = (term647 A f s x).
Proof. exact (TRANS (@lem3760979 A f s x) (@lem3760974 A f s x)). Qed.
Lemma lem3760981 {A : Type'} (f : type686 A) (s : A -> Prop) : (term655 A f s) = (term656 A f s).
Proof. exact (fun_ext (fun x : A => @lem3760980 A f s x)). Qed.
Lemma lem3760982 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3760983 {A : Type'} (f : type686 A) (s : A -> Prop) : (term652 A f s) = (term657 A f s).
Proof. exact (MK_COMB (@lem3760982 A) (@lem3760981 A f s)). Qed.
Lemma lem3760984 {A : Type'} (f : type686 A) (s : A -> Prop) : (term651 A f s) = (term657 A f s).
Proof. exact (TRANS (@lem3760976 A f s) (@lem3760983 A f s)). Qed.
Lemma lem3760995 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term624 A f t x) = (term625 A f t x).
Proof. exact (@lem17045 (f t) (t x)). Qed.
Lemma lem3760998 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term526 A f t x) = (term526 A f t x).
Proof. exact (eq_refl (term526 A f t x)). Qed.
Lemma lem3760999 {A : Type'} (P : type686 A) : (term626 A P) = (term509 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3761000 {A : Type'} (f : type686 A) (x : A) : (term627 A f x) = (term628 A f x).
Proof. exact (@lem3760999 A (term528 A f x)). Qed.
Lemma lem3761001 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term629 A f x t) = (term526 A f t x).
Proof. exact (eq_refl (term629 A f x t)). Qed.
Lemma lem3761002 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3761003 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term630 A f x t) = (term624 A f t x).
Proof. exact (MK_COMB (@lem3761002) (@lem3761001 A f t x)). Qed.
Lemma lem3761004 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term630 A f x t) = (term625 A f t x).
Proof. exact (TRANS (@lem3761003 A f t x) (@lem3760995 A f t x)). Qed.
Lemma lem3761005 {A : Type'} (f : type686 A) (x : A) : (term631 A f x) = (term632 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761004 A f t x)). Qed.
Lemma lem3761006 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3761007 {A : Type'} (f : type686 A) (x : A) : (term628 A f x) = (term633 A f x).
Proof. exact (MK_COMB (@lem3761006 A) (@lem3761005 A f x)). Qed.
Lemma lem3761008 {A : Type'} (f : type686 A) (x : A) : (term627 A f x) = (term633 A f x).
Proof. exact (TRANS (@lem3761000 A f x) (@lem3761007 A f x)). Qed.
Lemma lem3761009 {A : Type'} (f : type686 A) (x : A) : (term528 A f x) = (term528 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3760998 A f t x)). Qed.
Lemma lem3761010 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761011 {A : Type'} (f : type686 A) (x : A) : (term529 A f x) = (term529 A f x).
Proof. exact (MK_COMB (@lem3761010 A) (@lem3761009 A f x)). Qed.
Lemma lem3761013 {A : Type'} (s : A -> Prop) (x : A) : (term634 A s x) = (term634 A s x).
Proof. exact (eq_refl (term634 A s x)). Qed.
Lemma lem3761014 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term635 A s f x) = (term636 A s f x).
Proof. exact (MK_COMB (@lem3761013 A s x) (@lem3761008 A f x)). Qed.
Lemma lem3761015 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term637 A s f x) = (term635 A s f x).
Proof. exact (@lem17160 (s x) (term529 A f x)). Qed.
Lemma lem3761016 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term637 A s f x) = (term636 A s f x).
Proof. exact (TRANS (@lem3761015 A s f x) (@lem3761014 A s f x)). Qed.
Lemma lem3761018 {A : Type'} (s : A -> Prop) (x : A) : (term520 A s x) = (term520 A s x).
Proof. exact (eq_refl (term520 A s x)). Qed.
Lemma lem3761019 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term530 A s f x) = (term530 A s f x).
Proof. exact (MK_COMB (@lem3761018 A s x) (@lem3761011 A f x)). Qed.
Lemma lem3761028 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term624 A f t x) = (term625 A f t x).
Proof. exact (@lem17045 (f t) (t x)). Qed.
Lemma lem3761031 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term526 A f t x) = (term526 A f t x).
Proof. exact (eq_refl (term526 A f t x)). Qed.
Lemma lem3761032 {A : Type'} (P : type686 A) : (term626 A P) = (term509 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3761033 {A : Type'} (f : type686 A) (x : A) : (term627 A f x) = (term628 A f x).
Proof. exact (@lem3761032 A (term528 A f x)). Qed.
Lemma lem3761034 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term629 A f x t) = (term526 A f t x).
Proof. exact (eq_refl (term629 A f x t)). Qed.
Lemma lem3761035 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3761036 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term630 A f x t) = (term624 A f t x).
Proof. exact (MK_COMB (@lem3761035) (@lem3761034 A f t x)). Qed.
Lemma lem3761037 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term630 A f x t) = (term625 A f t x).
Proof. exact (TRANS (@lem3761036 A f t x) (@lem3761028 A f t x)). Qed.
Lemma lem3761038 {A : Type'} (f : type686 A) (x : A) : (term631 A f x) = (term632 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761037 A f t x)). Qed.
Lemma lem3761039 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3761040 {A : Type'} (f : type686 A) (x : A) : (term628 A f x) = (term633 A f x).
Proof. exact (MK_COMB (@lem3761039 A) (@lem3761038 A f x)). Qed.
Lemma lem3761041 {A : Type'} (f : type686 A) (x : A) : (term627 A f x) = (term633 A f x).
Proof. exact (TRANS (@lem3761033 A f x) (@lem3761040 A f x)). Qed.
Lemma lem3761042 {A : Type'} (f : type686 A) (x : A) : (term528 A f x) = (term528 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761031 A f t x)). Qed.
Lemma lem3761043 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761044 {A : Type'} (f : type686 A) (x : A) : (term529 A f x) = (term529 A f x).
Proof. exact (MK_COMB (@lem3761043 A) (@lem3761042 A f x)). Qed.
Lemma lem3761045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761046 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term639 A s f x) = (term640 A s f x).
Proof. exact (MK_COMB (@lem3761045) (@lem3761016 A s f x)). Qed.
Lemma lem3761047 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term658 A s f x) = (term659 A s f x).
Proof. exact (MK_COMB (@lem3761046 A s f x) (@lem3761044 A f x)). Qed.
Lemma lem3761048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761049 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term643 A s f x) = (term643 A s f x).
Proof. exact (MK_COMB (@lem3761048) (@lem3761019 A s f x)). Qed.
Lemma lem3761050 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term660 A s f x) = (term661 A s f x).
Proof. exact (MK_COMB (@lem3761049 A s f x) (@lem3761041 A f x)). Qed.
Lemma lem3761051 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761052 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term662 A s f x) = (term663 A s f x).
Proof. exact (MK_COMB (@lem3761051) (@lem3761050 A s f x)). Qed.
Lemma lem3761053 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term664 A s f x) = (term665 A s f x).
Proof. exact (MK_COMB (@lem3761052 A s f x) (@lem3761047 A s f x)). Qed.
Lemma lem3761054 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term666 A s f x) = (term664 A s f x).
Proof. exact (@lem17646 (term530 A s f x) (term529 A f x)). Qed.
Lemma lem3761055 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term666 A s f x) = (term665 A s f x).
Proof. exact (TRANS (@lem3761054 A s f x) (@lem3761053 A s f x)). Qed.
Lemma lem3761056 {A : Type'} (P : A -> Prop) : (term649 A P) = (term650 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3761057 {A : Type'} (s : A -> Prop) (f : type686 A) : (term667 A s f) = (term668 A s f).
Proof. exact (@lem3761056 A (term538 A s f)). Qed.
Lemma lem3761058 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term669 A s f x) = ((term530 A s f x) = (term529 A f x)).
Proof. exact (eq_refl (term669 A s f x)). Qed.
Lemma lem3761059 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3761060 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term670 A s f x) = (term666 A s f x).
Proof. exact (MK_COMB (@lem3761059) (@lem3761058 A s f x)). Qed.
Lemma lem3761061 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term670 A s f x) = (term665 A s f x).
Proof. exact (TRANS (@lem3761060 A s f x) (@lem3761055 A s f x)). Qed.
Lemma lem3761062 {A : Type'} (s : A -> Prop) (f : type686 A) : (term671 A s f) = (term672 A s f).
Proof. exact (fun_ext (fun x : A => @lem3761061 A s f x)). Qed.
Lemma lem3761063 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761064 {A : Type'} (s : A -> Prop) (f : type686 A) : (term668 A s f) = (term673 A s f).
Proof. exact (MK_COMB (@lem3761063 A) (@lem3761062 A s f)). Qed.
Lemma lem3761065 {A : Type'} (s : A -> Prop) (f : type686 A) : (term667 A s f) = (term673 A s f).
Proof. exact (TRANS (@lem3761057 A s f) (@lem3761064 A s f)). Qed.
Lemma lem3761066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761067 {A : Type'} (f : type686 A) (s : A -> Prop) : (term674 A f s) = (term675 A f s).
Proof. exact (MK_COMB (@lem3761066) (@lem3760984 A f s)). Qed.
Lemma lem3761068 {A : Type'} (s : A -> Prop) (f : type686 A) : (term676 A s f) = (term677 A s f).
Proof. exact (MK_COMB (@lem3761067 A f s) (@lem3761065 A s f)). Qed.
Lemma lem3761069 {A : Type'} (s : A -> Prop) (f : type686 A) : (term557 A s f) = (term676 A s f).
Proof. exact (@lem17160 (term535 A f s) (term539 A s f)). Qed.
Lemma lem3761070 {A : Type'} (s : A -> Prop) (f : type686 A) : (term557 A s f) = (term677 A s f).
Proof. exact (TRANS (@lem3761069 A s f) (@lem3761068 A s f)). Qed.
Lemma lem3761072 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term678 A P Q) = (term679 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3761073 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term678 A P Q) = (term679 A P Q).
Proof. exact (@lem3761072 A P Q). Qed.
Lemma lem3761074 {A : Type'} (f : type686 A) (s : A -> Prop) : (term680 A f s) = (term681 A f s).
Proof. exact (@lem3761073 A (term682 A f s) (term683 A f s)). Qed.
Lemma lem3761075 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term684 A f s x) = (term644 A f s x).
Proof. exact (eq_refl (term684 A f s x)). Qed.
Lemma lem3761076 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761077 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term685 A f s x) = (term645 A f s x).
Proof. exact (MK_COMB (@lem3761076) (@lem3761075 A f s x)). Qed.
Lemma lem3761078 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term686 A f s x) = (term642 A f s x).
Proof. exact (eq_refl (term686 A f s x)). Qed.
Lemma lem3761079 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term687 A f s x) = (term647 A f s x).
Proof. exact (MK_COMB (@lem3761077 A f s x) (@lem3761078 A f s x)). Qed.
Lemma lem3761080 {A : Type'} (f : type686 A) (s : A -> Prop) : (term688 A f s) = (term656 A f s).
Proof. exact (fun_ext (fun x : A => @lem3761079 A f s x)). Qed.
Lemma lem3761081 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761082 {A : Type'} (f : type686 A) (s : A -> Prop) : (term680 A f s) = (term657 A f s).
Proof. exact (MK_COMB (@lem3761081 A) (@lem3761080 A f s)). Qed.
Lemma lem3761083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3761084 {A : Type'} (f : type686 A) (s : A -> Prop) : (term689 A f s) = (term690 A f s).
Proof. exact (MK_COMB (@lem3761083) (@lem3761082 A f s)). Qed.
Lemma lem3761085 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term684 A f s x) = (term644 A f s x).
Proof. exact (eq_refl (term684 A f s x)). Qed.
Lemma lem3761086 {A : Type'} (f : type686 A) (s : A -> Prop) : (term691 A f s) = (term682 A f s).
Proof. exact (fun_ext (fun x : A => @lem3761085 A f s x)). Qed.
Lemma lem3761087 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761088 {A : Type'} (f : type686 A) (s : A -> Prop) : (term692 A f s) = (term693 A f s).
Proof. exact (MK_COMB (@lem3761087 A) (@lem3761086 A f s)). Qed.
Lemma lem3761089 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761090 {A : Type'} (f : type686 A) (s : A -> Prop) : (term694 A f s) = (term695 A f s).
Proof. exact (MK_COMB (@lem3761089) (@lem3761088 A f s)). Qed.
Lemma lem3761091 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term686 A f s x) = (term642 A f s x).
Proof. exact (eq_refl (term686 A f s x)). Qed.
Lemma lem3761092 {A : Type'} (f : type686 A) (s : A -> Prop) : (term696 A f s) = (term683 A f s).
Proof. exact (fun_ext (fun x : A => @lem3761091 A f s x)). Qed.
Lemma lem3761093 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761094 {A : Type'} (f : type686 A) (s : A -> Prop) : (term697 A f s) = (term698 A f s).
Proof. exact (MK_COMB (@lem3761093 A) (@lem3761092 A f s)). Qed.
Lemma lem3761095 {A : Type'} (f : type686 A) (s : A -> Prop) : (term681 A f s) = (term699 A f s).
Proof. exact (MK_COMB (@lem3761090 A f s) (@lem3761094 A f s)). Qed.
Lemma lem3761096 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term680 A f s) = (term681 A f s)) = ((term657 A f s) = (term699 A f s)).
Proof. exact (MK_COMB (@lem3761084 A f s) (@lem3761095 A f s)). Qed.
Lemma lem3761097 {A : Type'} (f : type686 A) (s : A -> Prop) : (term657 A f s) = (term699 A f s).
Proof. exact (EQ_MP (@lem3761096 A f s) (@lem3761074 A f s)). Qed.
Lemma lem3761254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761255 {A : Type'} (f : type686 A) (s : A -> Prop) : (term675 A f s) = (term700 A f s).
Proof. exact (MK_COMB (@lem3761254) (@lem3761097 A f s)). Qed.
Lemma lem3761257 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term678 A P Q) = (term679 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3761258 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term678 A P Q) = (term679 A P Q).
Proof. exact (@lem3761257 A P Q). Qed.
Lemma lem3761259 {A : Type'} (s : A -> Prop) (f : type686 A) : (term701 A s f) = (term702 A s f).
Proof. exact (@lem3761258 A (term703 A s f) (term704 A s f)). Qed.
Lemma lem3761260 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term705 A s f x) = (term661 A s f x).
Proof. exact (eq_refl (term705 A s f x)). Qed.
Lemma lem3761261 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761262 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term706 A s f x) = (term663 A s f x).
Proof. exact (MK_COMB (@lem3761261) (@lem3761260 A s f x)). Qed.
Lemma lem3761263 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term707 A s f x) = (term659 A s f x).
Proof. exact (eq_refl (term707 A s f x)). Qed.
Lemma lem3761264 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term708 A s f x) = (term665 A s f x).
Proof. exact (MK_COMB (@lem3761262 A s f x) (@lem3761263 A s f x)). Qed.
Lemma lem3761265 {A : Type'} (s : A -> Prop) (f : type686 A) : (term709 A s f) = (term672 A s f).
Proof. exact (fun_ext (fun x : A => @lem3761264 A s f x)). Qed.
Lemma lem3761266 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761267 {A : Type'} (s : A -> Prop) (f : type686 A) : (term701 A s f) = (term673 A s f).
Proof. exact (MK_COMB (@lem3761266 A) (@lem3761265 A s f)). Qed.
Lemma lem3761268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3761269 {A : Type'} (s : A -> Prop) (f : type686 A) : (term710 A s f) = (term711 A s f).
Proof. exact (MK_COMB (@lem3761268) (@lem3761267 A s f)). Qed.
Lemma lem3761270 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term705 A s f x) = (term661 A s f x).
Proof. exact (eq_refl (term705 A s f x)). Qed.
Lemma lem3761271 {A : Type'} (s : A -> Prop) (f : type686 A) : (term712 A s f) = (term703 A s f).
Proof. exact (fun_ext (fun x : A => @lem3761270 A s f x)). Qed.
Lemma lem3761272 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761273 {A : Type'} (s : A -> Prop) (f : type686 A) : (term713 A s f) = (term714 A s f).
Proof. exact (MK_COMB (@lem3761272 A) (@lem3761271 A s f)). Qed.
Lemma lem3761274 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761275 {A : Type'} (s : A -> Prop) (f : type686 A) : (term715 A s f) = (term716 A s f).
Proof. exact (MK_COMB (@lem3761274) (@lem3761273 A s f)). Qed.
Lemma lem3761276 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term707 A s f x) = (term659 A s f x).
Proof. exact (eq_refl (term707 A s f x)). Qed.
Lemma lem3761277 {A : Type'} (s : A -> Prop) (f : type686 A) : (term717 A s f) = (term704 A s f).
Proof. exact (fun_ext (fun x : A => @lem3761276 A s f x)). Qed.
Lemma lem3761278 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761279 {A : Type'} (s : A -> Prop) (f : type686 A) : (term718 A s f) = (term719 A s f).
Proof. exact (MK_COMB (@lem3761278 A) (@lem3761277 A s f)). Qed.
Lemma lem3761280 {A : Type'} (s : A -> Prop) (f : type686 A) : (term702 A s f) = (term720 A s f).
Proof. exact (MK_COMB (@lem3761275 A s f) (@lem3761279 A s f)). Qed.
Lemma lem3761281 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term701 A s f) = (term702 A s f)) = ((term673 A s f) = (term720 A s f)).
Proof. exact (MK_COMB (@lem3761269 A s f) (@lem3761280 A s f)). Qed.
Lemma lem3761282 {A : Type'} (s : A -> Prop) (f : type686 A) : (term673 A s f) = (term720 A s f).
Proof. exact (EQ_MP (@lem3761281 A s f) (@lem3761259 A s f)). Qed.
Lemma lem3761531 {A : Type'} (s : A -> Prop) (f : type686 A) : (term677 A s f) = (term721 A s f).
Proof. exact (MK_COMB (@lem3761255 A f s) (@lem3761282 A s f)). Qed.
Lemma lem3761533 {A : Type'} (P : Prop) (Q : A -> Prop) : (term722 A P Q) = (term723 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3761534 {A : Type'} (P : Prop) (Q : type686 A) : (term724 A P Q) = (term725 A P Q).
Proof. exact (@lem3761533 (A -> Prop) P Q). Qed.
Lemma lem3761535 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term726 A s f x) = (term727 A s f x).
Proof. exact (@lem3761534 A (s x) (term528 A f x)). Qed.
Lemma lem3761536 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term629 A f x t) = (term526 A f t x).
Proof. exact (eq_refl (term629 A f x t)). Qed.
Lemma lem3761537 {A : Type'} (f : type686 A) (x : A) : (term728 A f x) = (term528 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761536 A f t x)). Qed.
Lemma lem3761538 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761539 {A : Type'} (f : type686 A) (x : A) : (term729 A f x) = (term529 A f x).
Proof. exact (MK_COMB (@lem3761538 A) (@lem3761537 A f x)). Qed.
Lemma lem3761540 {A : Type'} (s : A -> Prop) (x : A) : (term520 A s x) = (term520 A s x).
Proof. exact (eq_refl (term520 A s x)). Qed.
Lemma lem3761541 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term726 A s f x) = (term530 A s f x).
Proof. exact (MK_COMB (@lem3761540 A s x) (@lem3761539 A f x)). Qed.
Lemma lem3761542 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3761543 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term730 A s f x) = (term532 A s f x).
Proof. exact (MK_COMB (@lem3761542) (@lem3761541 A s f x)). Qed.
Lemma lem3761544 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term629 A f x t) = (term526 A f t x).
Proof. exact (eq_refl (term629 A f x t)). Qed.
Lemma lem3761545 {A : Type'} (s : A -> Prop) (x : A) : (term520 A s x) = (term520 A s x).
Proof. exact (eq_refl (term520 A s x)). Qed.
Lemma lem3761546 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term731 A s f x t) = (term732 A s f t x).
Proof. exact (MK_COMB (@lem3761545 A s x) (@lem3761544 A f t x)). Qed.
Lemma lem3761547 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term733 A s f x) = (term734 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761546 A s f t x)). Qed.
Lemma lem3761548 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761549 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term727 A s f x) = (term735 A s f x).
Proof. exact (MK_COMB (@lem3761548 A) (@lem3761547 A s f x)). Qed.
Lemma lem3761550 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term726 A s f x) = (term727 A s f x)) = ((term530 A s f x) = (term735 A s f x)).
Proof. exact (MK_COMB (@lem3761543 A s f x) (@lem3761549 A s f x)). Qed.
Lemma lem3761551 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term530 A s f x) = (term735 A s f x).
Proof. exact (EQ_MP (@lem3761550 A s f x) (@lem3761535 A s f x)). Qed.
Lemma lem3761552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761553 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term643 A s f x) = (term736 A s f x).
Proof. exact (MK_COMB (@lem3761552) (@lem3761551 A s f x)). Qed.
Lemma lem3761554 {A : Type'} (s : A -> Prop) (x : A) : (term638 A s x) = (term638 A s x).
Proof. exact (eq_refl (term638 A s x)). Qed.
Lemma lem3761555 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term644 A f s x) = (term737 A f s x).
Proof. exact (MK_COMB (@lem3761553 A s f x) (@lem3761554 A s x)). Qed.
Lemma lem3761557 {A : Type'} (P : A -> Prop) (Q : Prop) : (term738 A P Q) = (term739 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3761558 {A : Type'} (P : type686 A) (Q : Prop) : (term740 A P Q) = (term741 A P Q).
Proof. exact (@lem3761557 (A -> Prop) P Q). Qed.
Lemma lem3761559 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term742 A f s x) = (term743 A f s x).
Proof. exact (@lem3761558 A (term734 A s f x) (term638 A s x)). Qed.
Lemma lem3761560 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term744 A s f x t) = (term732 A s f t x).
Proof. exact (eq_refl (term744 A s f x t)). Qed.
Lemma lem3761561 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term745 A s f x) = (term734 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761560 A s f t x)). Qed.
Lemma lem3761562 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761563 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term746 A s f x) = (term735 A s f x).
Proof. exact (MK_COMB (@lem3761562 A) (@lem3761561 A s f x)). Qed.
Lemma lem3761564 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761565 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term747 A s f x) = (term736 A s f x).
Proof. exact (MK_COMB (@lem3761564) (@lem3761563 A s f x)). Qed.
Lemma lem3761566 {A : Type'} (s : A -> Prop) (x : A) : (term638 A s x) = (term638 A s x).
Proof. exact (eq_refl (term638 A s x)). Qed.
Lemma lem3761567 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term742 A f s x) = (term737 A f s x).
Proof. exact (MK_COMB (@lem3761565 A s f x) (@lem3761566 A s x)). Qed.
Lemma lem3761568 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3761569 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term748 A f s x) = (term749 A f s x).
Proof. exact (MK_COMB (@lem3761568) (@lem3761567 A f s x)). Qed.
Lemma lem3761570 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term744 A s f x t) = (term732 A s f t x).
Proof. exact (eq_refl (term744 A s f x t)). Qed.
Lemma lem3761571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761572 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term750 A s f x t) = (term751 A s f t x).
Proof. exact (MK_COMB (@lem3761571) (@lem3761570 A s f t x)). Qed.
Lemma lem3761573 {A : Type'} (s : A -> Prop) (x : A) : (term638 A s x) = (term638 A s x).
Proof. exact (eq_refl (term638 A s x)). Qed.
Lemma lem3761574 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term752 A f t s x) = (term753 A f t s x).
Proof. exact (MK_COMB (@lem3761572 A s f t x) (@lem3761573 A s x)). Qed.
Lemma lem3761575 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term754 A f s x) = (term755 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761574 A f t s x)). Qed.
Lemma lem3761576 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761577 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term743 A f s x) = (term756 A f s x).
Proof. exact (MK_COMB (@lem3761576 A) (@lem3761575 A f s x)). Qed.
Lemma lem3761578 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term742 A f s x) = (term743 A f s x)) = ((term737 A f s x) = (term756 A f s x)).
Proof. exact (MK_COMB (@lem3761569 A f s x) (@lem3761577 A f s x)). Qed.
Lemma lem3761579 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term737 A f s x) = (term756 A f s x).
Proof. exact (EQ_MP (@lem3761578 A f s x) (@lem3761559 A f s x)). Qed.
Lemma lem3761580 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term644 A f s x) = (term756 A f s x).
Proof. exact (TRANS (@lem3761555 A f s x) (@lem3761579 A f s x)). Qed.
Lemma lem3761581 {A : Type'} (f : type686 A) (s : A -> Prop) : (term682 A f s) = (term757 A f s).
Proof. exact (fun_ext (fun x : A => @lem3761580 A f s x)). Qed.
Lemma lem3761582 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761583 {A : Type'} (f : type686 A) (s : A -> Prop) : (term693 A f s) = (term758 A f s).
Proof. exact (MK_COMB (@lem3761582 A) (@lem3761581 A f s)). Qed.
Lemma lem3761584 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761585 {A : Type'} (f : type686 A) (s : A -> Prop) : (term695 A f s) = (term759 A f s).
Proof. exact (MK_COMB (@lem3761584) (@lem3761583 A f s)). Qed.
Lemma lem3761586 {A : Type'} (f : type686 A) (s : A -> Prop) : (term698 A f s) = (term698 A f s).
Proof. exact (eq_refl (term698 A f s)). Qed.
Lemma lem3761587 {A : Type'} (f : type686 A) (s : A -> Prop) : (term699 A f s) = (term760 A f s).
Proof. exact (MK_COMB (@lem3761585 A f s) (@lem3761586 A f s)). Qed.
Lemma lem3761589 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term679 A P Q) = (term678 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3761590 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term679 A P Q) = (term678 A P Q).
Proof. exact (@lem3761589 A P Q). Qed.
Lemma lem3761591 {A : Type'} (f : type686 A) (s : A -> Prop) : (term761 A f s) = (term762 A f s).
Proof. exact (@lem3761590 A (term757 A f s) (term683 A f s)). Qed.
Lemma lem3761592 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term763 A f s x) = (term756 A f s x).
Proof. exact (eq_refl (term763 A f s x)). Qed.
Lemma lem3761593 {A : Type'} (f : type686 A) (s : A -> Prop) : (term764 A f s) = (term757 A f s).
Proof. exact (fun_ext (fun x : A => @lem3761592 A f s x)). Qed.
Lemma lem3761594 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761595 {A : Type'} (f : type686 A) (s : A -> Prop) : (term765 A f s) = (term758 A f s).
Proof. exact (MK_COMB (@lem3761594 A) (@lem3761593 A f s)). Qed.
Lemma lem3761596 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761597 {A : Type'} (f : type686 A) (s : A -> Prop) : (term766 A f s) = (term759 A f s).
Proof. exact (MK_COMB (@lem3761596) (@lem3761595 A f s)). Qed.
Lemma lem3761598 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term686 A f s x) = (term642 A f s x).
Proof. exact (eq_refl (term686 A f s x)). Qed.
Lemma lem3761599 {A : Type'} (f : type686 A) (s : A -> Prop) : (term696 A f s) = (term683 A f s).
Proof. exact (fun_ext (fun x : A => @lem3761598 A f s x)). Qed.
Lemma lem3761600 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761601 {A : Type'} (f : type686 A) (s : A -> Prop) : (term697 A f s) = (term698 A f s).
Proof. exact (MK_COMB (@lem3761600 A) (@lem3761599 A f s)). Qed.
Lemma lem3761602 {A : Type'} (f : type686 A) (s : A -> Prop) : (term761 A f s) = (term760 A f s).
Proof. exact (MK_COMB (@lem3761597 A f s) (@lem3761601 A f s)). Qed.
Lemma lem3761603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3761604 {A : Type'} (f : type686 A) (s : A -> Prop) : (term767 A f s) = (term768 A f s).
Proof. exact (MK_COMB (@lem3761603) (@lem3761602 A f s)). Qed.
Lemma lem3761605 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term763 A f s x) = (term756 A f s x).
Proof. exact (eq_refl (term763 A f s x)). Qed.
Lemma lem3761606 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761607 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term769 A f s x) = (term770 A f s x).
Proof. exact (MK_COMB (@lem3761606) (@lem3761605 A f s x)). Qed.
Lemma lem3761608 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term686 A f s x) = (term642 A f s x).
Proof. exact (eq_refl (term686 A f s x)). Qed.
Lemma lem3761609 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term771 A f s x) = (term772 A f s x).
Proof. exact (MK_COMB (@lem3761607 A f s x) (@lem3761608 A f s x)). Qed.
Lemma lem3761610 {A : Type'} (f : type686 A) (s : A -> Prop) : (term773 A f s) = (term774 A f s).
Proof. exact (fun_ext (fun x : A => @lem3761609 A f s x)). Qed.
Lemma lem3761611 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761612 {A : Type'} (f : type686 A) (s : A -> Prop) : (term762 A f s) = (term775 A f s).
Proof. exact (MK_COMB (@lem3761611 A) (@lem3761610 A f s)). Qed.
Lemma lem3761613 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term761 A f s) = (term762 A f s)) = ((term760 A f s) = (term775 A f s)).
Proof. exact (MK_COMB (@lem3761604 A f s) (@lem3761612 A f s)). Qed.
Lemma lem3761614 {A : Type'} (f : type686 A) (s : A -> Prop) : (term760 A f s) = (term775 A f s).
Proof. exact (EQ_MP (@lem3761613 A f s) (@lem3761591 A f s)). Qed.
Lemma lem3761616 {A : Type'} (P : A -> Prop) (Q : Prop) : (term776 A P Q) = (term777 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3761617 {A : Type'} (P : type686 A) (Q : Prop) : (term778 A P Q) = (term779 A P Q).
Proof. exact (@lem3761616 (A -> Prop) P Q). Qed.
Lemma lem3761618 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term780 A f s x) = (term781 A f s x).
Proof. exact (@lem3761617 A (term755 A f s x) (term642 A f s x)). Qed.
Lemma lem3761619 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term782 A f s x t) = (term753 A f t s x).
Proof. exact (eq_refl (term782 A f s x t)). Qed.
Lemma lem3761620 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term783 A f s x) = (term755 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761619 A f t s x)). Qed.
Lemma lem3761621 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761622 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term784 A f s x) = (term756 A f s x).
Proof. exact (MK_COMB (@lem3761621 A) (@lem3761620 A f s x)). Qed.
Lemma lem3761623 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761624 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term785 A f s x) = (term770 A f s x).
Proof. exact (MK_COMB (@lem3761623) (@lem3761622 A f s x)). Qed.
Lemma lem3761625 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term642 A f s x) = (term642 A f s x).
Proof. exact (eq_refl (term642 A f s x)). Qed.
Lemma lem3761626 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term780 A f s x) = (term772 A f s x).
Proof. exact (MK_COMB (@lem3761624 A f s x) (@lem3761625 A f s x)). Qed.
Lemma lem3761627 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3761628 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term786 A f s x) = (term787 A f s x).
Proof. exact (MK_COMB (@lem3761627) (@lem3761626 A f s x)). Qed.
Lemma lem3761629 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term782 A f s x t) = (term753 A f t s x).
Proof. exact (eq_refl (term782 A f s x t)). Qed.
Lemma lem3761630 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761631 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term788 A f s x t) = (term789 A f t s x).
Proof. exact (MK_COMB (@lem3761630) (@lem3761629 A f t s x)). Qed.
Lemma lem3761632 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term642 A f s x) = (term642 A f s x).
Proof. exact (eq_refl (term642 A f s x)). Qed.
Lemma lem3761633 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term790 A t f s x) = (term791 A t f s x).
Proof. exact (MK_COMB (@lem3761631 A f t s x) (@lem3761632 A f s x)). Qed.
Lemma lem3761634 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term792 A f s x) = (term793 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761633 A t f s x)). Qed.
Lemma lem3761635 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761636 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term781 A f s x) = (term794 A f s x).
Proof. exact (MK_COMB (@lem3761635 A) (@lem3761634 A f s x)). Qed.
Lemma lem3761637 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : ((term780 A f s x) = (term781 A f s x)) = ((term772 A f s x) = (term794 A f s x)).
Proof. exact (MK_COMB (@lem3761628 A f s x) (@lem3761636 A f s x)). Qed.
Lemma lem3761638 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term772 A f s x) = (term794 A f s x).
Proof. exact (EQ_MP (@lem3761637 A f s x) (@lem3761618 A f s x)). Qed.
Lemma lem3761639 {A : Type'} (f : type686 A) (s : A -> Prop) : (term774 A f s) = (term795 A f s).
Proof. exact (fun_ext (fun x : A => @lem3761638 A f s x)). Qed.
Lemma lem3761640 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761641 {A : Type'} (f : type686 A) (s : A -> Prop) : (term775 A f s) = (term796 A f s).
Proof. exact (MK_COMB (@lem3761640 A) (@lem3761639 A f s)). Qed.
Lemma lem3761642 {A : Type'} (f : type686 A) (s : A -> Prop) : (term760 A f s) = (term796 A f s).
Proof. exact (TRANS (@lem3761614 A f s) (@lem3761641 A f s)). Qed.
Lemma lem3761643 {A : Type'} (f : type686 A) (s : A -> Prop) : (term699 A f s) = (term796 A f s).
Proof. exact (TRANS (@lem3761587 A f s) (@lem3761642 A f s)). Qed.
Lemma lem3761644 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761645 {A : Type'} (f : type686 A) (s : A -> Prop) : (term700 A f s) = (term797 A f s).
Proof. exact (MK_COMB (@lem3761644) (@lem3761643 A f s)). Qed.
Lemma lem3761647 {A : Type'} (P : Prop) (Q : A -> Prop) : (term722 A P Q) = (term723 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3761648 {A : Type'} (P : Prop) (Q : type686 A) : (term724 A P Q) = (term725 A P Q).
Proof. exact (@lem3761647 (A -> Prop) P Q). Qed.
Lemma lem3761649 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term726 A s f x) = (term727 A s f x).
Proof. exact (@lem3761648 A (s x) (term528 A f x)). Qed.
Lemma lem3761650 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term629 A f x t) = (term526 A f t x).
Proof. exact (eq_refl (term629 A f x t)). Qed.
Lemma lem3761651 {A : Type'} (f : type686 A) (x : A) : (term728 A f x) = (term528 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761650 A f t x)). Qed.
Lemma lem3761652 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761653 {A : Type'} (f : type686 A) (x : A) : (term729 A f x) = (term529 A f x).
Proof. exact (MK_COMB (@lem3761652 A) (@lem3761651 A f x)). Qed.
Lemma lem3761654 {A : Type'} (s : A -> Prop) (x : A) : (term520 A s x) = (term520 A s x).
Proof. exact (eq_refl (term520 A s x)). Qed.
Lemma lem3761655 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term726 A s f x) = (term530 A s f x).
Proof. exact (MK_COMB (@lem3761654 A s x) (@lem3761653 A f x)). Qed.
Lemma lem3761656 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3761657 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term730 A s f x) = (term532 A s f x).
Proof. exact (MK_COMB (@lem3761656) (@lem3761655 A s f x)). Qed.
Lemma lem3761658 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term629 A f x t) = (term526 A f t x).
Proof. exact (eq_refl (term629 A f x t)). Qed.
Lemma lem3761659 {A : Type'} (s : A -> Prop) (x : A) : (term520 A s x) = (term520 A s x).
Proof. exact (eq_refl (term520 A s x)). Qed.
Lemma lem3761660 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term731 A s f x t) = (term732 A s f t x).
Proof. exact (MK_COMB (@lem3761659 A s x) (@lem3761658 A f t x)). Qed.
Lemma lem3761661 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term733 A s f x) = (term734 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761660 A s f t x)). Qed.
Lemma lem3761662 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761663 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term727 A s f x) = (term735 A s f x).
Proof. exact (MK_COMB (@lem3761662 A) (@lem3761661 A s f x)). Qed.
Lemma lem3761664 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term726 A s f x) = (term727 A s f x)) = ((term530 A s f x) = (term735 A s f x)).
Proof. exact (MK_COMB (@lem3761657 A s f x) (@lem3761663 A s f x)). Qed.
Lemma lem3761665 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term530 A s f x) = (term735 A s f x).
Proof. exact (EQ_MP (@lem3761664 A s f x) (@lem3761649 A s f x)). Qed.
Lemma lem3761666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761667 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term643 A s f x) = (term736 A s f x).
Proof. exact (MK_COMB (@lem3761666) (@lem3761665 A s f x)). Qed.
Lemma lem3761668 {A : Type'} (f : type686 A) (x : A) : (term633 A f x) = (term633 A f x).
Proof. exact (eq_refl (term633 A f x)). Qed.
Lemma lem3761669 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term661 A s f x) = (term798 A s f x).
Proof. exact (MK_COMB (@lem3761667 A s f x) (@lem3761668 A f x)). Qed.
Lemma lem3761671 {A : Type'} (P : A -> Prop) (Q : Prop) : (term738 A P Q) = (term739 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3761672 {A : Type'} (P : type686 A) (Q : Prop) : (term740 A P Q) = (term741 A P Q).
Proof. exact (@lem3761671 (A -> Prop) P Q). Qed.
Lemma lem3761673 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term799 A s f x) = (term800 A s f x).
Proof. exact (@lem3761672 A (term734 A s f x) (term633 A f x)). Qed.
Lemma lem3761674 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term744 A s f x t) = (term732 A s f t x).
Proof. exact (eq_refl (term744 A s f x t)). Qed.
Lemma lem3761675 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term745 A s f x) = (term734 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761674 A s f t x)). Qed.
Lemma lem3761676 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761677 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term746 A s f x) = (term735 A s f x).
Proof. exact (MK_COMB (@lem3761676 A) (@lem3761675 A s f x)). Qed.
Lemma lem3761678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761679 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term747 A s f x) = (term736 A s f x).
Proof. exact (MK_COMB (@lem3761678) (@lem3761677 A s f x)). Qed.
Lemma lem3761680 {A : Type'} (f : type686 A) (x : A) : (term633 A f x) = (term633 A f x).
Proof. exact (eq_refl (term633 A f x)). Qed.
Lemma lem3761681 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term799 A s f x) = (term798 A s f x).
Proof. exact (MK_COMB (@lem3761679 A s f x) (@lem3761680 A f x)). Qed.
Lemma lem3761682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3761683 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term801 A s f x) = (term802 A s f x).
Proof. exact (MK_COMB (@lem3761682) (@lem3761681 A s f x)). Qed.
Lemma lem3761684 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term744 A s f x t) = (term732 A s f t x).
Proof. exact (eq_refl (term744 A s f x t)). Qed.
Lemma lem3761685 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761686 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term750 A s f x t) = (term751 A s f t x).
Proof. exact (MK_COMB (@lem3761685) (@lem3761684 A s f t x)). Qed.
Lemma lem3761687 {A : Type'} (f : type686 A) (x : A) : (term633 A f x) = (term633 A f x).
Proof. exact (eq_refl (term633 A f x)). Qed.
Lemma lem3761688 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : type686 A) (x : A) : (term803 A s t f x) = (term804 A s t f x).
Proof. exact (MK_COMB (@lem3761686 A s f t x) (@lem3761687 A f x)). Qed.
Lemma lem3761689 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term805 A s f x) = (term806 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761688 A s t f x)). Qed.
Lemma lem3761690 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761691 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term800 A s f x) = (term807 A s f x).
Proof. exact (MK_COMB (@lem3761690 A) (@lem3761689 A s f x)). Qed.
Lemma lem3761692 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term799 A s f x) = (term800 A s f x)) = ((term798 A s f x) = (term807 A s f x)).
Proof. exact (MK_COMB (@lem3761683 A s f x) (@lem3761691 A s f x)). Qed.
Lemma lem3761693 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term798 A s f x) = (term807 A s f x).
Proof. exact (EQ_MP (@lem3761692 A s f x) (@lem3761673 A s f x)). Qed.
Lemma lem3761694 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term661 A s f x) = (term807 A s f x).
Proof. exact (TRANS (@lem3761669 A s f x) (@lem3761693 A s f x)). Qed.
Lemma lem3761695 {A : Type'} (s : A -> Prop) (f : type686 A) : (term703 A s f) = (term808 A s f).
Proof. exact (fun_ext (fun x : A => @lem3761694 A s f x)). Qed.
Lemma lem3761696 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761697 {A : Type'} (s : A -> Prop) (f : type686 A) : (term714 A s f) = (term809 A s f).
Proof. exact (MK_COMB (@lem3761696 A) (@lem3761695 A s f)). Qed.
Lemma lem3761698 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761699 {A : Type'} (s : A -> Prop) (f : type686 A) : (term716 A s f) = (term810 A s f).
Proof. exact (MK_COMB (@lem3761698) (@lem3761697 A s f)). Qed.
Lemma lem3761701 {A : Type'} (P : Prop) (Q : A -> Prop) : (term591 A P Q) = (term592 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3761702 {A : Type'} (P : Prop) (Q : type686 A) : (term593 A P Q) = (term594 A P Q).
Proof. exact (@lem3761701 (A -> Prop) P Q). Qed.
Lemma lem3761703 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term811 A s f x) = (term812 A s f x).
Proof. exact (@lem3761702 A (term636 A s f x) (term528 A f x)). Qed.
Lemma lem3761704 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term629 A f x t) = (term526 A f t x).
Proof. exact (eq_refl (term629 A f x t)). Qed.
Lemma lem3761705 {A : Type'} (f : type686 A) (x : A) : (term728 A f x) = (term528 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761704 A f t x)). Qed.
Lemma lem3761706 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761707 {A : Type'} (f : type686 A) (x : A) : (term729 A f x) = (term529 A f x).
Proof. exact (MK_COMB (@lem3761706 A) (@lem3761705 A f x)). Qed.
Lemma lem3761708 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term640 A s f x) = (term640 A s f x).
Proof. exact (eq_refl (term640 A s f x)). Qed.
Lemma lem3761709 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term811 A s f x) = (term659 A s f x).
Proof. exact (MK_COMB (@lem3761708 A s f x) (@lem3761707 A f x)). Qed.
Lemma lem3761710 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3761711 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term813 A s f x) = (term814 A s f x).
Proof. exact (MK_COMB (@lem3761710) (@lem3761709 A s f x)). Qed.
Lemma lem3761712 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term629 A f x t) = (term526 A f t x).
Proof. exact (eq_refl (term629 A f x t)). Qed.
Lemma lem3761713 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term640 A s f x) = (term640 A s f x).
Proof. exact (eq_refl (term640 A s f x)). Qed.
Lemma lem3761714 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term815 A s f x t) = (term816 A s f t x).
Proof. exact (MK_COMB (@lem3761713 A s f x) (@lem3761712 A f t x)). Qed.
Lemma lem3761715 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term817 A s f x) = (term818 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761714 A s f t x)). Qed.
Lemma lem3761716 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761717 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term812 A s f x) = (term819 A s f x).
Proof. exact (MK_COMB (@lem3761716 A) (@lem3761715 A s f x)). Qed.
Lemma lem3761718 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term811 A s f x) = (term812 A s f x)) = ((term659 A s f x) = (term819 A s f x)).
Proof. exact (MK_COMB (@lem3761711 A s f x) (@lem3761717 A s f x)). Qed.
Lemma lem3761719 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term659 A s f x) = (term819 A s f x).
Proof. exact (EQ_MP (@lem3761718 A s f x) (@lem3761703 A s f x)). Qed.
Lemma lem3761720 {A : Type'} (s : A -> Prop) (f : type686 A) : (term704 A s f) = (term820 A s f).
Proof. exact (fun_ext (fun x : A => @lem3761719 A s f x)). Qed.
Lemma lem3761721 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761722 {A : Type'} (s : A -> Prop) (f : type686 A) : (term719 A s f) = (term821 A s f).
Proof. exact (MK_COMB (@lem3761721 A) (@lem3761720 A s f)). Qed.
Lemma lem3761723 {A : Type'} (s : A -> Prop) (f : type686 A) : (term720 A s f) = (term822 A s f).
Proof. exact (MK_COMB (@lem3761699 A s f) (@lem3761722 A s f)). Qed.
Lemma lem3761725 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term679 A P Q) = (term678 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3761726 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term679 A P Q) = (term678 A P Q).
Proof. exact (@lem3761725 A P Q). Qed.
Lemma lem3761727 {A : Type'} (s : A -> Prop) (f : type686 A) : (term823 A s f) = (term824 A s f).
Proof. exact (@lem3761726 A (term808 A s f) (term820 A s f)). Qed.
Lemma lem3761728 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term825 A s f x) = (term807 A s f x).
Proof. exact (eq_refl (term825 A s f x)). Qed.
Lemma lem3761729 {A : Type'} (s : A -> Prop) (f : type686 A) : (term826 A s f) = (term808 A s f).
Proof. exact (fun_ext (fun x : A => @lem3761728 A s f x)). Qed.
Lemma lem3761730 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761731 {A : Type'} (s : A -> Prop) (f : type686 A) : (term827 A s f) = (term809 A s f).
Proof. exact (MK_COMB (@lem3761730 A) (@lem3761729 A s f)). Qed.
Lemma lem3761732 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761733 {A : Type'} (s : A -> Prop) (f : type686 A) : (term828 A s f) = (term810 A s f).
Proof. exact (MK_COMB (@lem3761732) (@lem3761731 A s f)). Qed.
Lemma lem3761734 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term829 A s f x) = (term819 A s f x).
Proof. exact (eq_refl (term829 A s f x)). Qed.
Lemma lem3761735 {A : Type'} (s : A -> Prop) (f : type686 A) : (term830 A s f) = (term820 A s f).
Proof. exact (fun_ext (fun x : A => @lem3761734 A s f x)). Qed.
Lemma lem3761736 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761737 {A : Type'} (s : A -> Prop) (f : type686 A) : (term831 A s f) = (term821 A s f).
Proof. exact (MK_COMB (@lem3761736 A) (@lem3761735 A s f)). Qed.
Lemma lem3761738 {A : Type'} (s : A -> Prop) (f : type686 A) : (term823 A s f) = (term822 A s f).
Proof. exact (MK_COMB (@lem3761733 A s f) (@lem3761737 A s f)). Qed.
Lemma lem3761739 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3761740 {A : Type'} (s : A -> Prop) (f : type686 A) : (term832 A s f) = (term833 A s f).
Proof. exact (MK_COMB (@lem3761739) (@lem3761738 A s f)). Qed.
Lemma lem3761741 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term825 A s f x) = (term807 A s f x).
Proof. exact (eq_refl (term825 A s f x)). Qed.
Lemma lem3761742 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761743 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term834 A s f x) = (term835 A s f x).
Proof. exact (MK_COMB (@lem3761742) (@lem3761741 A s f x)). Qed.
Lemma lem3761744 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term829 A s f x) = (term819 A s f x).
Proof. exact (eq_refl (term829 A s f x)). Qed.
Lemma lem3761745 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term836 A s f x) = (term837 A s f x).
Proof. exact (MK_COMB (@lem3761743 A s f x) (@lem3761744 A s f x)). Qed.
Lemma lem3761746 {A : Type'} (s : A -> Prop) (f : type686 A) : (term838 A s f) = (term839 A s f).
Proof. exact (fun_ext (fun x : A => @lem3761745 A s f x)). Qed.
Lemma lem3761747 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761748 {A : Type'} (s : A -> Prop) (f : type686 A) : (term824 A s f) = (term840 A s f).
Proof. exact (MK_COMB (@lem3761747 A) (@lem3761746 A s f)). Qed.
Lemma lem3761749 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term823 A s f) = (term824 A s f)) = ((term822 A s f) = (term840 A s f)).
Proof. exact (MK_COMB (@lem3761740 A s f) (@lem3761748 A s f)). Qed.
Lemma lem3761750 {A : Type'} (s : A -> Prop) (f : type686 A) : (term822 A s f) = (term840 A s f).
Proof. exact (EQ_MP (@lem3761749 A s f) (@lem3761727 A s f)). Qed.
Lemma lem3761752 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term679 A P Q) = (term678 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3761753 {A : Type'} (P : type686 A) (Q : type686 A) : (term841 A P Q) = (term842 A P Q).
Proof. exact (@lem3761752 (A -> Prop) P Q). Qed.
Lemma lem3761754 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term843 A s f x) = (term844 A s f x).
Proof. exact (@lem3761753 A (term806 A s f x) (term818 A s f x)). Qed.
Lemma lem3761755 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : type686 A) (x : A) : (term845 A s f x t) = (term804 A s t f x).
Proof. exact (eq_refl (term845 A s f x t)). Qed.
Lemma lem3761756 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term846 A s f x) = (term806 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761755 A s t f x)). Qed.
Lemma lem3761757 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761758 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term847 A s f x) = (term807 A s f x).
Proof. exact (MK_COMB (@lem3761757 A) (@lem3761756 A s f x)). Qed.
Lemma lem3761759 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761760 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term848 A s f x) = (term835 A s f x).
Proof. exact (MK_COMB (@lem3761759) (@lem3761758 A s f x)). Qed.
Lemma lem3761761 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term849 A s f x t) = (term816 A s f t x).
Proof. exact (eq_refl (term849 A s f x t)). Qed.
Lemma lem3761762 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term850 A s f x) = (term818 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761761 A s f t x)). Qed.
Lemma lem3761763 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761764 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term851 A s f x) = (term819 A s f x).
Proof. exact (MK_COMB (@lem3761763 A) (@lem3761762 A s f x)). Qed.
Lemma lem3761765 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term843 A s f x) = (term837 A s f x).
Proof. exact (MK_COMB (@lem3761760 A s f x) (@lem3761764 A s f x)). Qed.
Lemma lem3761766 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3761767 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term852 A s f x) = (term853 A s f x).
Proof. exact (MK_COMB (@lem3761766) (@lem3761765 A s f x)). Qed.
Lemma lem3761768 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : type686 A) (x : A) : (term845 A s f x t) = (term804 A s t f x).
Proof. exact (eq_refl (term845 A s f x t)). Qed.
Lemma lem3761769 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761770 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : type686 A) (x : A) : (term854 A s f x t) = (term855 A s t f x).
Proof. exact (MK_COMB (@lem3761769) (@lem3761768 A s t f x)). Qed.
Lemma lem3761771 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term849 A s f x t) = (term816 A s f t x).
Proof. exact (eq_refl (term849 A s f x t)). Qed.
Lemma lem3761772 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term856 A s f x t) = (term857 A s f t x).
Proof. exact (MK_COMB (@lem3761770 A s t f x) (@lem3761771 A s f t x)). Qed.
Lemma lem3761773 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term858 A s f x) = (term859 A s f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761772 A s f t x)). Qed.
Lemma lem3761774 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761775 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term844 A s f x) = (term860 A s f x).
Proof. exact (MK_COMB (@lem3761774 A) (@lem3761773 A s f x)). Qed.
Lemma lem3761776 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : ((term843 A s f x) = (term844 A s f x)) = ((term837 A s f x) = (term860 A s f x)).
Proof. exact (MK_COMB (@lem3761767 A s f x) (@lem3761775 A s f x)). Qed.
Lemma lem3761777 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term837 A s f x) = (term860 A s f x).
Proof. exact (EQ_MP (@lem3761776 A s f x) (@lem3761754 A s f x)). Qed.
Lemma lem3761778 {A : Type'} (s : A -> Prop) (f : type686 A) : (term839 A s f) = (term861 A s f).
Proof. exact (fun_ext (fun x : A => @lem3761777 A s f x)). Qed.
Lemma lem3761779 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761780 {A : Type'} (s : A -> Prop) (f : type686 A) : (term840 A s f) = (term862 A s f).
Proof. exact (MK_COMB (@lem3761779 A) (@lem3761778 A s f)). Qed.
Lemma lem3761781 {A : Type'} (s : A -> Prop) (f : type686 A) : (term822 A s f) = (term862 A s f).
Proof. exact (TRANS (@lem3761750 A s f) (@lem3761780 A s f)). Qed.
Lemma lem3761782 {A : Type'} (s : A -> Prop) (f : type686 A) : (term720 A s f) = (term862 A s f).
Proof. exact (TRANS (@lem3761723 A s f) (@lem3761781 A s f)). Qed.
Lemma lem3761783 {A : Type'} (s : A -> Prop) (f : type686 A) : (term721 A s f) = (term863 A s f).
Proof. exact (MK_COMB (@lem3761645 A f s) (@lem3761782 A s f)). Qed.
Lemma lem3761785 {A : Type'} (P : A -> Prop) (Q : Prop) : (term738 A P Q) = (term739 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3761786 {A : Type'} (P : A -> Prop) (Q : Prop) : (term738 A P Q) = (term739 A P Q).
Proof. exact (@lem3761785 A P Q). Qed.
Lemma lem3761787 {A : Type'} (s : A -> Prop) (f : type686 A) : (term864 A s f) = (term865 A s f).
Proof. exact (@lem3761786 A (term795 A f s) (term862 A s f)). Qed.
Lemma lem3761788 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term866 A f s x) = (term794 A f s x).
Proof. exact (eq_refl (term866 A f s x)). Qed.
Lemma lem3761789 {A : Type'} (f : type686 A) (s : A -> Prop) : (term867 A f s) = (term795 A f s).
Proof. exact (fun_ext (fun x : A => @lem3761788 A f s x)). Qed.
Lemma lem3761790 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761791 {A : Type'} (f : type686 A) (s : A -> Prop) : (term868 A f s) = (term796 A f s).
Proof. exact (MK_COMB (@lem3761790 A) (@lem3761789 A f s)). Qed.
Lemma lem3761792 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761793 {A : Type'} (f : type686 A) (s : A -> Prop) : (term869 A f s) = (term797 A f s).
Proof. exact (MK_COMB (@lem3761792) (@lem3761791 A f s)). Qed.
Lemma lem3761794 {A : Type'} (s : A -> Prop) (f : type686 A) : (term862 A s f) = (term862 A s f).
Proof. exact (eq_refl (term862 A s f)). Qed.
Lemma lem3761795 {A : Type'} (s : A -> Prop) (f : type686 A) : (term864 A s f) = (term863 A s f).
Proof. exact (MK_COMB (@lem3761793 A f s) (@lem3761794 A s f)). Qed.
Lemma lem3761796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3761797 {A : Type'} (s : A -> Prop) (f : type686 A) : (term870 A s f) = (term871 A s f).
Proof. exact (MK_COMB (@lem3761796) (@lem3761795 A s f)). Qed.
Lemma lem3761798 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term866 A f s x) = (term794 A f s x).
Proof. exact (eq_refl (term866 A f s x)). Qed.
Lemma lem3761799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761800 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term872 A f s x) = (term873 A f s x).
Proof. exact (MK_COMB (@lem3761799) (@lem3761798 A f s x)). Qed.
Lemma lem3761801 {A : Type'} (s : A -> Prop) (f : type686 A) : (term862 A s f) = (term862 A s f).
Proof. exact (eq_refl (term862 A s f)). Qed.
Lemma lem3761802 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term874 A x s f) = (term875 A x s f).
Proof. exact (MK_COMB (@lem3761800 A f s x) (@lem3761801 A s f)). Qed.
Lemma lem3761803 {A : Type'} (s : A -> Prop) (f : type686 A) : (term876 A s f) = (term877 A s f).
Proof. exact (fun_ext (fun x : A => @lem3761802 A x s f)). Qed.
Lemma lem3761804 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761805 {A : Type'} (s : A -> Prop) (f : type686 A) : (term865 A s f) = (term878 A s f).
Proof. exact (MK_COMB (@lem3761804 A) (@lem3761803 A s f)). Qed.
Lemma lem3761806 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term864 A s f) = (term865 A s f)) = ((term863 A s f) = (term878 A s f)).
Proof. exact (MK_COMB (@lem3761797 A s f) (@lem3761805 A s f)). Qed.
Lemma lem3761807 {A : Type'} (s : A -> Prop) (f : type686 A) : (term863 A s f) = (term878 A s f).
Proof. exact (EQ_MP (@lem3761806 A s f) (@lem3761787 A s f)). Qed.
Lemma lem3761809 {A : Type'} (P : A -> Prop) (Q : Prop) : (term738 A P Q) = (term739 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3761810 {A : Type'} (P : type686 A) (Q : Prop) : (term740 A P Q) = (term741 A P Q).
Proof. exact (@lem3761809 (A -> Prop) P Q). Qed.
Lemma lem3761811 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term879 A x s f) = (term880 A x s f).
Proof. exact (@lem3761810 A (term793 A f s x) (term862 A s f)). Qed.
Lemma lem3761812 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term881 A f s x t) = (term791 A t f s x).
Proof. exact (eq_refl (term881 A f s x t)). Qed.
Lemma lem3761813 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term882 A f s x) = (term793 A f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761812 A t f s x)). Qed.
Lemma lem3761814 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761815 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term883 A f s x) = (term794 A f s x).
Proof. exact (MK_COMB (@lem3761814 A) (@lem3761813 A f s x)). Qed.
Lemma lem3761816 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761817 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term884 A f s x) = (term873 A f s x).
Proof. exact (MK_COMB (@lem3761816) (@lem3761815 A f s x)). Qed.
Lemma lem3761818 {A : Type'} (s : A -> Prop) (f : type686 A) : (term862 A s f) = (term862 A s f).
Proof. exact (eq_refl (term862 A s f)). Qed.
Lemma lem3761819 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term879 A x s f) = (term875 A x s f).
Proof. exact (MK_COMB (@lem3761817 A f s x) (@lem3761818 A s f)). Qed.
Lemma lem3761820 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3761821 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term885 A x s f) = (term886 A x s f).
Proof. exact (MK_COMB (@lem3761820) (@lem3761819 A x s f)). Qed.
Lemma lem3761822 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term881 A f s x t) = (term791 A t f s x).
Proof. exact (eq_refl (term881 A f s x t)). Qed.
Lemma lem3761823 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761824 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term887 A f s x t) = (term888 A t f s x).
Proof. exact (MK_COMB (@lem3761823) (@lem3761822 A t f s x)). Qed.
Lemma lem3761825 {A : Type'} (s : A -> Prop) (f : type686 A) : (term862 A s f) = (term862 A s f).
Proof. exact (eq_refl (term862 A s f)). Qed.
Lemma lem3761826 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term889 A x t s f) = (term890 A t x s f).
Proof. exact (MK_COMB (@lem3761824 A t f s x) (@lem3761825 A s f)). Qed.
Lemma lem3761827 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term891 A x s f) = (term892 A x s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761826 A t x s f)). Qed.
Lemma lem3761828 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761829 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term880 A x s f) = (term893 A x s f).
Proof. exact (MK_COMB (@lem3761828 A) (@lem3761827 A x s f)). Qed.
Lemma lem3761830 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : ((term879 A x s f) = (term880 A x s f)) = ((term875 A x s f) = (term893 A x s f)).
Proof. exact (MK_COMB (@lem3761821 A x s f) (@lem3761829 A x s f)). Qed.
Lemma lem3761831 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term875 A x s f) = (term893 A x s f).
Proof. exact (EQ_MP (@lem3761830 A x s f) (@lem3761811 A x s f)). Qed.
Lemma lem3761833 {A : Type'} (P : Prop) (Q : A -> Prop) : (term591 A P Q) = (term592 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3761834 {A : Type'} (P : Prop) (Q : A -> Prop) : (term591 A P Q) = (term592 A P Q).
Proof. exact (@lem3761833 A P Q). Qed.
Lemma lem3761835 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term894 A t x s f) = (term895 A t x s f).
Proof. exact (@lem3761834 A (term791 A t f s x) (term861 A s f)). Qed.
Lemma lem3761836 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term896 A s f x) = (term860 A s f x).
Proof. exact (eq_refl (term896 A s f x)). Qed.
Lemma lem3761837 {A : Type'} (s : A -> Prop) (f : type686 A) : (term897 A s f) = (term861 A s f).
Proof. exact (fun_ext (fun x : A => @lem3761836 A s f x)). Qed.
Lemma lem3761838 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761839 {A : Type'} (s : A -> Prop) (f : type686 A) : (term898 A s f) = (term862 A s f).
Proof. exact (MK_COMB (@lem3761838 A) (@lem3761837 A s f)). Qed.
Lemma lem3761840 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term888 A t f s x) = (term888 A t f s x).
Proof. exact (eq_refl (term888 A t f s x)). Qed.
Lemma lem3761841 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term894 A t x s f) = (term890 A t x s f).
Proof. exact (MK_COMB (@lem3761840 A t f s x) (@lem3761839 A s f)). Qed.
Lemma lem3761842 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3761843 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term899 A t x s f) = (term900 A t x s f).
Proof. exact (MK_COMB (@lem3761842) (@lem3761841 A t x s f)). Qed.
Lemma lem3761844 {A : Type'} (s : A -> Prop) (f : type686 A) (x' : A) : (term896 A s f x') = (term860 A s f x').
Proof. exact (eq_refl (term896 A s f x')). Qed.
Lemma lem3761845 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term888 A t f s x) = (term888 A t f s x).
Proof. exact (eq_refl (term888 A t f s x)). Qed.
Lemma lem3761846 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) : (term901 A t x s f x') = (term902 A t x s f x').
Proof. exact (MK_COMB (@lem3761845 A t f s x) (@lem3761844 A s f x')). Qed.
Lemma lem3761847 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term903 A t x s f) = (term904 A t x s f).
Proof. exact (fun_ext (fun x' : A => @lem3761846 A t x s f x')). Qed.
Lemma lem3761848 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761849 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term895 A t x s f) = (term905 A t x s f).
Proof. exact (MK_COMB (@lem3761848 A) (@lem3761847 A t x s f)). Qed.
Lemma lem3761850 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : ((term894 A t x s f) = (term895 A t x s f)) = ((term890 A t x s f) = (term905 A t x s f)).
Proof. exact (MK_COMB (@lem3761843 A t x s f) (@lem3761849 A t x s f)). Qed.
Lemma lem3761851 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term890 A t x s f) = (term905 A t x s f).
Proof. exact (EQ_MP (@lem3761850 A t x s f) (@lem3761835 A t x s f)). Qed.
Lemma lem3761853 {A : Type'} (P : Prop) (Q : A -> Prop) : (term591 A P Q) = (term592 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3761854 {A : Type'} (P : Prop) (Q : type686 A) : (term593 A P Q) = (term594 A P Q).
Proof. exact (@lem3761853 (A -> Prop) P Q). Qed.
Lemma lem3761855 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) : (term906 A t x s f x') = (term907 A t x s f x').
Proof. exact (@lem3761854 A (term791 A t f s x) (term859 A s f x')). Qed.
Lemma lem3761856 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x' : A) : (term908 A s f x' t) = (term857 A s f t x').
Proof. exact (eq_refl (term908 A s f x' t)). Qed.
Lemma lem3761857 {A : Type'} (s : A -> Prop) (f : type686 A) (x' : A) : (term909 A s f x') = (term859 A s f x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761856 A s f t x')). Qed.
Lemma lem3761858 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761859 {A : Type'} (s : A -> Prop) (f : type686 A) (x' : A) : (term910 A s f x') = (term860 A s f x').
Proof. exact (MK_COMB (@lem3761858 A) (@lem3761857 A s f x')). Qed.
Lemma lem3761860 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term888 A t f s x) = (term888 A t f s x).
Proof. exact (eq_refl (term888 A t f s x)). Qed.
Lemma lem3761861 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) : (term906 A t x s f x') = (term902 A t x s f x').
Proof. exact (MK_COMB (@lem3761860 A t f s x) (@lem3761859 A s f x')). Qed.
Lemma lem3761862 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3761863 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) : (term911 A t x s f x') = (term912 A t x s f x').
Proof. exact (MK_COMB (@lem3761862) (@lem3761861 A t x s f x')). Qed.
Lemma lem3761864 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) : (term908 A s f x' t') = (term857 A s f t' x').
Proof. exact (eq_refl (term908 A s f x' t')). Qed.
Lemma lem3761865 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term888 A t f s x) = (term888 A t f s x).
Proof. exact (eq_refl (term888 A t f s x)). Qed.
Lemma lem3761866 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) : (term913 A t x s f x' t') = (term914 A t x s f t' x').
Proof. exact (MK_COMB (@lem3761865 A t f s x) (@lem3761864 A s f t' x')). Qed.
Lemma lem3761867 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) : (term915 A t x s f x') = (term916 A t x s f x').
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3761866 A t x s f t' x')). Qed.
Lemma lem3761868 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761869 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) : (term907 A t x s f x') = (term917 A t x s f x').
Proof. exact (MK_COMB (@lem3761868 A) (@lem3761867 A t x s f x')). Qed.
Lemma lem3761870 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) : ((term906 A t x s f x') = (term907 A t x s f x')) = ((term902 A t x s f x') = (term917 A t x s f x')).
Proof. exact (MK_COMB (@lem3761863 A t x s f x') (@lem3761869 A t x s f x')). Qed.
Lemma lem3761871 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) : (term902 A t x s f x') = (term917 A t x s f x').
Proof. exact (EQ_MP (@lem3761870 A t x s f x') (@lem3761855 A t x s f x')). Qed.
Lemma lem3761872 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term904 A t x s f) = (term918 A t x s f).
Proof. exact (fun_ext (fun x' : A => @lem3761871 A t x s f x')). Qed.
Lemma lem3761873 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761874 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term905 A t x s f) = (term919 A t x s f).
Proof. exact (MK_COMB (@lem3761873 A) (@lem3761872 A t x s f)). Qed.
Lemma lem3761875 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) : (term890 A t x s f) = (term919 A t x s f).
Proof. exact (TRANS (@lem3761851 A t x s f) (@lem3761874 A t x s f)). Qed.
Lemma lem3761876 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term892 A x s f) = (term920 A x s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761875 A t x s f)). Qed.
Lemma lem3761877 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3761878 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term893 A x s f) = (term921 A x s f).
Proof. exact (MK_COMB (@lem3761877 A) (@lem3761876 A x s f)). Qed.
Lemma lem3761879 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) : (term875 A x s f) = (term921 A x s f).
Proof. exact (TRANS (@lem3761831 A x s f) (@lem3761878 A x s f)). Qed.
Lemma lem3761880 {A : Type'} (s : A -> Prop) (f : type686 A) : (term877 A s f) = (term922 A s f).
Proof. exact (fun_ext (fun x : A => @lem3761879 A x s f)). Qed.
Lemma lem3761881 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3761882 {A : Type'} (s : A -> Prop) (f : type686 A) : (term878 A s f) = (term923 A s f).
Proof. exact (MK_COMB (@lem3761881 A) (@lem3761880 A s f)). Qed.
Lemma lem3761883 {A : Type'} (s : A -> Prop) (f : type686 A) : (term863 A s f) = (term923 A s f).
Proof. exact (TRANS (@lem3761807 A s f) (@lem3761882 A s f)). Qed.
Lemma lem3761884 {A : Type'} (s : A -> Prop) (f : type686 A) : (term721 A s f) = (term923 A s f).
Proof. exact (TRANS (@lem3761783 A s f) (@lem3761883 A s f)). Qed.
Lemma lem3761885 {A : Type'} (s : A -> Prop) (f : type686 A) : (term677 A s f) = (term923 A s f).
Proof. exact (TRANS (@lem3761531 A s f) (@lem3761884 A s f)). Qed.
Lemma lem3761886 {A : Type'} (s : A -> Prop) (f : type686 A) : (term557 A s f) = (term923 A s f).
Proof. exact (TRANS (@lem3761070 A s f) (@lem3761885 A s f)). Qed.
Lemma lem3761887 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term557 A s f) : term923 A s f.
Proof. exact (EQ_MP (@lem3761886 A s f) (@lem3760357 A s f h1)). Qed.
Lemma lem3761888 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) (h1 : term921 A x s f) : term921 A x s f.
Proof. exact (h1). Qed.
Lemma lem3761889 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (h1 : term919 A t x s f) : term919 A t x s f.
Proof. exact (h1). Qed.
Lemma lem3761890 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x' : A) (h1 : term917 A t x s f x') : term917 A t x s f x'.
Proof. exact (h1). Qed.
Lemma lem3761891 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term914 A t x s f t' x') : term914 A t x s f t' x'.
Proof. exact (h1). Qed.
Lemma lem3761892 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term620 A s f x''.
Proof. exact (h1). Qed.
Lemma lem3761897 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3761898 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3761897 A Prop f x). Qed.
Lemma lem3761900 {A : Type'} (t' : A -> Prop) (x' : A) : (t' x') = (@I (A -> Prop) t' x').
Proof. exact (@lem3761898 A t' x'). Qed.
Lemma lem3761905 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3761906 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3761905 (A -> Prop) Prop f x). Qed.
Lemma lem3761908 {A : Type'} (f : type686 A) (t' : A -> Prop) : (f t') = (@I ((A -> Prop) -> Prop) f t').
Proof. exact (@lem3761906 A f t'). Qed.
Lemma lem3761909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761910 {A : Type'} (f : type686 A) (t' : A -> Prop) : (term524 A f t') = (term924 A f t').
Proof. exact (MK_COMB (@lem3761909) (@lem3761908 A f t')). Qed.
Lemma lem3761911 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) : (term526 A f t' x') = (term925 A f t' x').
Proof. exact (MK_COMB (@lem3761910 A f t') (@lem3761900 A t' x')). Qed.
Lemma lem3761912 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3761917 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3761918 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3761917 A Prop f x). Qed.
Lemma lem3761920 {A : Type'} (t : A -> Prop) (x' : A) : (t x') = (@I (A -> Prop) t x').
Proof. exact (@lem3761918 A t x'). Qed.
Lemma lem3761921 {A : Type'} (t : A -> Prop) (x' : A) : (term638 A t x') = (term926 A t x').
Proof. exact (MK_COMB (@lem3761912) (@lem3761920 A t x')). Qed.
Lemma lem3761922 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3761927 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3761928 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3761927 (A -> Prop) Prop f x). Qed.
Lemma lem3761930 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3761928 A f t). Qed.
Lemma lem3761931 {A : Type'} (f : type686 A) (t : A -> Prop) : (term506 A f t) = (term927 A f t).
Proof. exact (MK_COMB (@lem3761922) (@lem3761930 A f t)). Qed.
Lemma lem3761932 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761933 {A : Type'} (f : type686 A) (t : A -> Prop) : (term563 A f t) = (term928 A f t).
Proof. exact (MK_COMB (@lem3761932) (@lem3761931 A f t)). Qed.
Lemma lem3761934 {A : Type'} (f : type686 A) (t : A -> Prop) (x' : A) : (term625 A f t x') = (term929 A f t x').
Proof. exact (MK_COMB (@lem3761933 A f t) (@lem3761921 A t x')). Qed.
Lemma lem3761935 {A : Type'} (f : type686 A) (x' : A) : (term632 A f x') = (term930 A f x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761934 A f t x')). Qed.
Lemma lem3761936 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3761937 {A : Type'} (f : type686 A) (x' : A) : (term633 A f x') = (term931 A f x').
Proof. exact (MK_COMB (@lem3761936 A) (@lem3761935 A f x')). Qed.
Lemma lem3761938 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3761943 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3761944 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3761943 A Prop f x). Qed.
Lemma lem3761946 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem3761944 A s x'). Qed.
Lemma lem3761947 {A : Type'} (s : A -> Prop) (x' : A) : (term638 A s x') = (term926 A s x').
Proof. exact (MK_COMB (@lem3761938) (@lem3761946 A s x')). Qed.
Lemma lem3761948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761949 {A : Type'} (s : A -> Prop) (x' : A) : (term634 A s x') = (term932 A s x').
Proof. exact (MK_COMB (@lem3761948) (@lem3761947 A s x')). Qed.
Lemma lem3761950 {A : Type'} (s : A -> Prop) (f : type686 A) (x' : A) : (term636 A s f x') = (term933 A s f x').
Proof. exact (MK_COMB (@lem3761949 A s x') (@lem3761937 A f x')). Qed.
Lemma lem3761951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761952 {A : Type'} (s : A -> Prop) (f : type686 A) (x' : A) : (term640 A s f x') = (term934 A s f x').
Proof. exact (MK_COMB (@lem3761951) (@lem3761950 A s f x')). Qed.
Lemma lem3761953 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) : (term816 A s f t' x') = (term935 A s f t' x').
Proof. exact (MK_COMB (@lem3761952 A s f x') (@lem3761911 A f t' x')). Qed.
Lemma lem3761954 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3761959 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3761960 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3761959 A Prop f x). Qed.
Lemma lem3761962 {A : Type'} (t : A -> Prop) (x' : A) : (t x') = (@I (A -> Prop) t x').
Proof. exact (@lem3761960 A t x'). Qed.
Lemma lem3761963 {A : Type'} (t : A -> Prop) (x' : A) : (term638 A t x') = (term926 A t x').
Proof. exact (MK_COMB (@lem3761954) (@lem3761962 A t x')). Qed.
Lemma lem3761964 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3761969 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3761970 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3761969 (A -> Prop) Prop f x). Qed.
Lemma lem3761972 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3761970 A f t). Qed.
Lemma lem3761973 {A : Type'} (f : type686 A) (t : A -> Prop) : (term506 A f t) = (term927 A f t).
Proof. exact (MK_COMB (@lem3761964) (@lem3761972 A f t)). Qed.
Lemma lem3761974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3761975 {A : Type'} (f : type686 A) (t : A -> Prop) : (term563 A f t) = (term928 A f t).
Proof. exact (MK_COMB (@lem3761974) (@lem3761973 A f t)). Qed.
Lemma lem3761976 {A : Type'} (f : type686 A) (t : A -> Prop) (x' : A) : (term625 A f t x') = (term929 A f t x').
Proof. exact (MK_COMB (@lem3761975 A f t) (@lem3761963 A t x')). Qed.
Lemma lem3761977 {A : Type'} (f : type686 A) (x' : A) : (term632 A f x') = (term930 A f x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3761976 A f t x')). Qed.
Lemma lem3761978 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3761979 {A : Type'} (f : type686 A) (x' : A) : (term633 A f x') = (term931 A f x').
Proof. exact (MK_COMB (@lem3761978 A) (@lem3761977 A f x')). Qed.
Lemma lem3761984 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3761985 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3761984 A Prop f x). Qed.
Lemma lem3761987 {A : Type'} (t' : A -> Prop) (x' : A) : (t' x') = (@I (A -> Prop) t' x').
Proof. exact (@lem3761985 A t' x'). Qed.
Lemma lem3761992 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3761993 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3761992 (A -> Prop) Prop f x). Qed.
Lemma lem3761995 {A : Type'} (f : type686 A) (t' : A -> Prop) : (f t') = (@I ((A -> Prop) -> Prop) f t').
Proof. exact (@lem3761993 A f t'). Qed.
Lemma lem3761996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3761997 {A : Type'} (f : type686 A) (t' : A -> Prop) : (term524 A f t') = (term924 A f t').
Proof. exact (MK_COMB (@lem3761996) (@lem3761995 A f t')). Qed.
Lemma lem3761998 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) : (term526 A f t' x') = (term925 A f t' x').
Proof. exact (MK_COMB (@lem3761997 A f t') (@lem3761987 A t' x')). Qed.
Lemma lem3762003 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762004 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762003 A Prop f x). Qed.
Lemma lem3762006 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem3762004 A s x'). Qed.
Lemma lem3762007 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762008 {A : Type'} (s : A -> Prop) (x' : A) : (term520 A s x') = (term936 A s x').
Proof. exact (MK_COMB (@lem3762007) (@lem3762006 A s x')). Qed.
Lemma lem3762009 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) : (term732 A s f t' x') = (term937 A s f t' x').
Proof. exact (MK_COMB (@lem3762008 A s x') (@lem3761998 A f t' x')). Qed.
Lemma lem3762010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3762011 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) : (term751 A s f t' x') = (term938 A s f t' x').
Proof. exact (MK_COMB (@lem3762010) (@lem3762009 A s f t' x')). Qed.
Lemma lem3762012 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) : (term804 A s t' f x') = (term939 A s t' f x').
Proof. exact (MK_COMB (@lem3762011 A s f t' x') (@lem3761979 A f x')). Qed.
Lemma lem3762013 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762014 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) : (term855 A s t' f x') = (term940 A s t' f x').
Proof. exact (MK_COMB (@lem3762013) (@lem3762012 A s t' f x')). Qed.
Lemma lem3762015 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) : (term857 A s f t' x') = (term941 A s f t' x').
Proof. exact (MK_COMB (@lem3762014 A s t' f x') (@lem3761953 A s f t' x')). Qed.
Lemma lem3762020 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762021 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762020 A Prop f x). Qed.
Lemma lem3762023 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3762021 A s x). Qed.
Lemma lem3762024 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3762029 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762030 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762029 A Prop f x). Qed.
Lemma lem3762032 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3762030 A t x). Qed.
Lemma lem3762033 {A : Type'} (t : A -> Prop) (x : A) : (term638 A t x) = (term926 A t x).
Proof. exact (MK_COMB (@lem3762024) (@lem3762032 A t x)). Qed.
Lemma lem3762034 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3762039 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762040 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3762039 (A -> Prop) Prop f x). Qed.
Lemma lem3762042 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3762040 A f t). Qed.
Lemma lem3762043 {A : Type'} (f : type686 A) (t : A -> Prop) : (term506 A f t) = (term927 A f t).
Proof. exact (MK_COMB (@lem3762034) (@lem3762042 A f t)). Qed.
Lemma lem3762044 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762045 {A : Type'} (f : type686 A) (t : A -> Prop) : (term563 A f t) = (term928 A f t).
Proof. exact (MK_COMB (@lem3762044) (@lem3762043 A f t)). Qed.
Lemma lem3762046 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term625 A f t x) = (term929 A f t x).
Proof. exact (MK_COMB (@lem3762045 A f t) (@lem3762033 A t x)). Qed.
Lemma lem3762047 {A : Type'} (f : type686 A) (x : A) : (term632 A f x) = (term930 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3762046 A f t x)). Qed.
Lemma lem3762048 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3762049 {A : Type'} (f : type686 A) (x : A) : (term633 A f x) = (term931 A f x).
Proof. exact (MK_COMB (@lem3762048 A) (@lem3762047 A f x)). Qed.
Lemma lem3762050 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3762055 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762056 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762055 A Prop f x). Qed.
Lemma lem3762058 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3762056 A s x). Qed.
Lemma lem3762059 {A : Type'} (s : A -> Prop) (x : A) : (term638 A s x) = (term926 A s x).
Proof. exact (MK_COMB (@lem3762050) (@lem3762058 A s x)). Qed.
Lemma lem3762060 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3762061 {A : Type'} (s : A -> Prop) (x : A) : (term634 A s x) = (term932 A s x).
Proof. exact (MK_COMB (@lem3762060) (@lem3762059 A s x)). Qed.
Lemma lem3762062 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term636 A s f x) = (term933 A s f x).
Proof. exact (MK_COMB (@lem3762061 A s x) (@lem3762049 A f x)). Qed.
Lemma lem3762063 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3762064 {A : Type'} (s : A -> Prop) (f : type686 A) (x : A) : (term640 A s f x) = (term934 A s f x).
Proof. exact (MK_COMB (@lem3762063) (@lem3762062 A s f x)). Qed.
Lemma lem3762065 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term642 A f s x) = (term942 A f s x).
Proof. exact (MK_COMB (@lem3762064 A s f x) (@lem3762023 A s x)). Qed.
Lemma lem3762066 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3762071 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762072 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762071 A Prop f x). Qed.
Lemma lem3762074 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3762072 A s x). Qed.
Lemma lem3762075 {A : Type'} (s : A -> Prop) (x : A) : (term638 A s x) = (term926 A s x).
Proof. exact (MK_COMB (@lem3762066) (@lem3762074 A s x)). Qed.
Lemma lem3762080 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762081 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762080 A Prop f x). Qed.
Lemma lem3762083 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3762081 A t x). Qed.
Lemma lem3762088 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762089 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3762088 (A -> Prop) Prop f x). Qed.
Lemma lem3762091 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3762089 A f t). Qed.
Lemma lem3762092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3762093 {A : Type'} (f : type686 A) (t : A -> Prop) : (term524 A f t) = (term924 A f t).
Proof. exact (MK_COMB (@lem3762092) (@lem3762091 A f t)). Qed.
Lemma lem3762094 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term526 A f t x) = (term925 A f t x).
Proof. exact (MK_COMB (@lem3762093 A f t) (@lem3762083 A t x)). Qed.
Lemma lem3762099 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762100 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762099 A Prop f x). Qed.
Lemma lem3762102 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3762100 A s x). Qed.
Lemma lem3762103 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762104 {A : Type'} (s : A -> Prop) (x : A) : (term520 A s x) = (term936 A s x).
Proof. exact (MK_COMB (@lem3762103) (@lem3762102 A s x)). Qed.
Lemma lem3762105 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term732 A s f t x) = (term937 A s f t x).
Proof. exact (MK_COMB (@lem3762104 A s x) (@lem3762094 A f t x)). Qed.
Lemma lem3762106 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3762107 {A : Type'} (s : A -> Prop) (f : type686 A) (t : A -> Prop) (x : A) : (term751 A s f t x) = (term938 A s f t x).
Proof. exact (MK_COMB (@lem3762106) (@lem3762105 A s f t x)). Qed.
Lemma lem3762108 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term753 A f t s x) = (term943 A f t s x).
Proof. exact (MK_COMB (@lem3762107 A s f t x) (@lem3762075 A s x)). Qed.
Lemma lem3762109 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762110 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term789 A f t s x) = (term944 A f t s x).
Proof. exact (MK_COMB (@lem3762109) (@lem3762108 A f t s x)). Qed.
Lemma lem3762111 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term791 A t f s x) = (term945 A t f s x).
Proof. exact (MK_COMB (@lem3762110 A f t s x) (@lem3762065 A f s x)). Qed.
Lemma lem3762112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3762113 {A : Type'} (t : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) : (term888 A t f s x) = (term946 A t f s x).
Proof. exact (MK_COMB (@lem3762112) (@lem3762111 A t f s x)). Qed.
Lemma lem3762114 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) : (term914 A t x s f t' x') = (term947 A t x s f t' x').
Proof. exact (MK_COMB (@lem3762113 A t f s x) (@lem3762015 A s f t' x')). Qed.
Lemma lem3762115 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term914 A t x s f t' x') : term947 A t x s f t' x'.
Proof. exact (EQ_MP (@lem3762114 A t x s f t' x') (@lem3761891 A t x s f t' x' h1)). Qed.
Lemma lem3762120 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762121 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3762120 (A -> Prop) Prop f x). Qed.
Lemma lem3762123 {A : Type'} (f : type686 A) (x'' : A -> Prop) : (f x'') = (@I ((A -> Prop) -> Prop) f x'').
Proof. exact (@lem3762121 A f x''). Qed.
Lemma lem3762128 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762129 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762128 A Prop f x). Qed.
Lemma lem3762131 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3762129 A s x). Qed.
Lemma lem3762132 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3762137 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762138 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762137 A Prop f x). Qed.
Lemma lem3762140 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3762138 A t x). Qed.
Lemma lem3762141 {A : Type'} (t : A -> Prop) (x : A) : (term638 A t x) = (term926 A t x).
Proof. exact (MK_COMB (@lem3762132) (@lem3762140 A t x)). Qed.
Lemma lem3762142 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762143 {A : Type'} (t : A -> Prop) (x : A) : (term948 A t x) = (term949 A t x).
Proof. exact (MK_COMB (@lem3762142) (@lem3762141 A t x)). Qed.
Lemma lem3762144 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term558 A t s x) = (term950 A t s x).
Proof. exact (MK_COMB (@lem3762143 A t x) (@lem3762131 A s x)). Qed.
Lemma lem3762145 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term559 A t s) = (term951 A t s).
Proof. exact (fun_ext (fun x : A => @lem3762144 A t s x)). Qed.
Lemma lem3762146 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3762147 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term560 A t s) = (term952 A t s).
Proof. exact (MK_COMB (@lem3762146 A) (@lem3762145 A t s)). Qed.
Lemma lem3762152 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762153 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762152 A Prop f x). Qed.
Lemma lem3762155 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3762153 A t x). Qed.
Lemma lem3762156 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3762161 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762162 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762161 A Prop f x). Qed.
Lemma lem3762164 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3762162 A s x). Qed.
Lemma lem3762165 {A : Type'} (s : A -> Prop) (x : A) : (term638 A s x) = (term926 A s x).
Proof. exact (MK_COMB (@lem3762156) (@lem3762164 A s x)). Qed.
Lemma lem3762166 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762167 {A : Type'} (s : A -> Prop) (x : A) : (term948 A s x) = (term949 A s x).
Proof. exact (MK_COMB (@lem3762166) (@lem3762165 A s x)). Qed.
Lemma lem3762168 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term558 A s t x) = (term950 A s t x).
Proof. exact (MK_COMB (@lem3762167 A s x) (@lem3762155 A t x)). Qed.
Lemma lem3762169 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term559 A s t) = (term951 A s t).
Proof. exact (fun_ext (fun x : A => @lem3762168 A s t x)). Qed.
Lemma lem3762170 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3762171 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term560 A s t) = (term952 A s t).
Proof. exact (MK_COMB (@lem3762170 A) (@lem3762169 A s t)). Qed.
Lemma lem3762172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762173 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term561 A s t) = (term953 A s t).
Proof. exact (MK_COMB (@lem3762172) (@lem3762171 A s t)). Qed.
Lemma lem3762174 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term562 A t s) = (term954 A t s).
Proof. exact (MK_COMB (@lem3762173 A s t) (@lem3762147 A t s)). Qed.
Lemma lem3762175 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3762180 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762181 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3762180 (A -> Prop) Prop f x). Qed.
Lemma lem3762183 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3762181 A f t). Qed.
Lemma lem3762184 {A : Type'} (f : type686 A) (t : A -> Prop) : (term506 A f t) = (term927 A f t).
Proof. exact (MK_COMB (@lem3762175) (@lem3762183 A f t)). Qed.
Lemma lem3762185 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762186 {A : Type'} (f : type686 A) (t : A -> Prop) : (term563 A f t) = (term928 A f t).
Proof. exact (MK_COMB (@lem3762185) (@lem3762184 A f t)). Qed.
Lemma lem3762187 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term565 A f t s) = (term955 A f t s).
Proof. exact (MK_COMB (@lem3762186 A f t) (@lem3762174 A t s)). Qed.
Lemma lem3762188 {A : Type'} (f : type686 A) (s : A -> Prop) : (term566 A f s) = (term956 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3762187 A f t s)). Qed.
Lemma lem3762189 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3762190 {A : Type'} (f : type686 A) (s : A -> Prop) : (term567 A f s) = (term957 A f s).
Proof. exact (MK_COMB (@lem3762189 A) (@lem3762188 A f s)). Qed.
Lemma lem3762191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3762192 {A : Type'} (f : type686 A) (s : A -> Prop) : (term585 A f s) = (term958 A f s).
Proof. exact (MK_COMB (@lem3762191) (@lem3762190 A f s)). Qed.
Lemma lem3762193 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) : (term601 A s f x'') = (term959 A s f x'').
Proof. exact (MK_COMB (@lem3762192 A f s) (@lem3762123 A f x'')). Qed.
Lemma lem3762198 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762199 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762198 A Prop f x). Qed.
Lemma lem3762201 {A : Type'} (s' : A -> Prop) (x : A) : (s' x) = (@I (A -> Prop) s' x).
Proof. exact (@lem3762199 A s' x). Qed.
Lemma lem3762202 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3762207 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762208 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762207 A Prop f x). Qed.
Lemma lem3762210 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3762208 A s x). Qed.
Lemma lem3762211 {A : Type'} (s : A -> Prop) (x : A) : (term638 A s x) = (term926 A s x).
Proof. exact (MK_COMB (@lem3762202) (@lem3762210 A s x)). Qed.
Lemma lem3762212 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762213 {A : Type'} (s : A -> Prop) (x : A) : (term948 A s x) = (term949 A s x).
Proof. exact (MK_COMB (@lem3762212) (@lem3762211 A s x)). Qed.
Lemma lem3762214 {A : Type'} (s : A -> Prop) (s' : A -> Prop) (x : A) : (term558 A s s' x) = (term950 A s s' x).
Proof. exact (MK_COMB (@lem3762213 A s x) (@lem3762201 A s' x)). Qed.
Lemma lem3762215 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term559 A s s') = (term951 A s s').
Proof. exact (fun_ext (fun x : A => @lem3762214 A s s' x)). Qed.
Lemma lem3762216 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3762217 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term560 A s s') = (term952 A s s').
Proof. exact (MK_COMB (@lem3762216 A) (@lem3762215 A s s')). Qed.
Lemma lem3762222 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762223 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762222 A Prop f x). Qed.
Lemma lem3762225 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3762223 A s x). Qed.
Lemma lem3762226 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3762231 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762232 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762231 A Prop f x). Qed.
Lemma lem3762234 {A : Type'} (s' : A -> Prop) (x : A) : (s' x) = (@I (A -> Prop) s' x).
Proof. exact (@lem3762232 A s' x). Qed.
Lemma lem3762235 {A : Type'} (s' : A -> Prop) (x : A) : (term638 A s' x) = (term926 A s' x).
Proof. exact (MK_COMB (@lem3762226) (@lem3762234 A s' x)). Qed.
Lemma lem3762236 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762237 {A : Type'} (s' : A -> Prop) (x : A) : (term948 A s' x) = (term949 A s' x).
Proof. exact (MK_COMB (@lem3762236) (@lem3762235 A s' x)). Qed.
Lemma lem3762238 {A : Type'} (s' : A -> Prop) (s : A -> Prop) (x : A) : (term558 A s' s x) = (term950 A s' s x).
Proof. exact (MK_COMB (@lem3762237 A s' x) (@lem3762225 A s x)). Qed.
Lemma lem3762239 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term559 A s' s) = (term951 A s' s).
Proof. exact (fun_ext (fun x : A => @lem3762238 A s' s x)). Qed.
Lemma lem3762240 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3762241 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term560 A s' s) = (term952 A s' s).
Proof. exact (MK_COMB (@lem3762240 A) (@lem3762239 A s' s)). Qed.
Lemma lem3762242 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762243 {A : Type'} (s' : A -> Prop) (s : A -> Prop) : (term561 A s' s) = (term953 A s' s).
Proof. exact (MK_COMB (@lem3762242) (@lem3762241 A s' s)). Qed.
Lemma lem3762244 {A : Type'} (s : A -> Prop) (s' : A -> Prop) : (term562 A s s') = (term954 A s s').
Proof. exact (MK_COMB (@lem3762243 A s' s) (@lem3762217 A s s')). Qed.
Lemma lem3762245 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3762250 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762251 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3762250 (A -> Prop) Prop f x). Qed.
Lemma lem3762253 {A : Type'} (f : type686 A) (s' : A -> Prop) : (f s') = (@I ((A -> Prop) -> Prop) f s').
Proof. exact (@lem3762251 A f s'). Qed.
Lemma lem3762254 {A : Type'} (f : type686 A) (s' : A -> Prop) : (term506 A f s') = (term927 A f s').
Proof. exact (MK_COMB (@lem3762245) (@lem3762253 A f s')). Qed.
Lemma lem3762255 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762256 {A : Type'} (f : type686 A) (s' : A -> Prop) : (term563 A f s') = (term928 A f s').
Proof. exact (MK_COMB (@lem3762255) (@lem3762254 A f s')). Qed.
Lemma lem3762257 {A : Type'} (f : type686 A) (s : A -> Prop) (s' : A -> Prop) : (term573 A f s s') = (term960 A f s s').
Proof. exact (MK_COMB (@lem3762256 A f s') (@lem3762244 A s s')). Qed.
Lemma lem3762258 {A : Type'} (f : type686 A) (s : A -> Prop) : (term574 A f s) = (term961 A f s).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3762257 A f s s')). Qed.
Lemma lem3762259 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3762260 {A : Type'} (f : type686 A) (s : A -> Prop) : (term575 A f s) = (term962 A f s).
Proof. exact (MK_COMB (@lem3762259 A) (@lem3762258 A f s)). Qed.
Lemma lem3762261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3762262 {A : Type'} (f : type686 A) (s : A -> Prop) : (term587 A f s) = (term963 A f s).
Proof. exact (MK_COMB (@lem3762261) (@lem3762260 A f s)). Qed.
Lemma lem3762263 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) : (term607 A s f x'') = (term964 A s f x'').
Proof. exact (MK_COMB (@lem3762262 A f s) (@lem3762193 A s f x'')). Qed.
Lemma lem3762268 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762269 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762268 A Prop f x). Qed.
Lemma lem3762271 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3762269 A s x). Qed.
Lemma lem3762272 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3762277 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762278 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762277 A Prop f x). Qed.
Lemma lem3762280 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3762278 A t x). Qed.
Lemma lem3762281 {A : Type'} (t : A -> Prop) (x : A) : (term638 A t x) = (term926 A t x).
Proof. exact (MK_COMB (@lem3762272) (@lem3762280 A t x)). Qed.
Lemma lem3762282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762283 {A : Type'} (t : A -> Prop) (x : A) : (term948 A t x) = (term949 A t x).
Proof. exact (MK_COMB (@lem3762282) (@lem3762281 A t x)). Qed.
Lemma lem3762284 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term558 A t s x) = (term950 A t s x).
Proof. exact (MK_COMB (@lem3762283 A t x) (@lem3762271 A s x)). Qed.
Lemma lem3762285 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term559 A t s) = (term951 A t s).
Proof. exact (fun_ext (fun x : A => @lem3762284 A t s x)). Qed.
Lemma lem3762286 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3762287 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term560 A t s) = (term952 A t s).
Proof. exact (MK_COMB (@lem3762286 A) (@lem3762285 A t s)). Qed.
Lemma lem3762292 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762293 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762292 A Prop f x). Qed.
Lemma lem3762295 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3762293 A t x). Qed.
Lemma lem3762296 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3762301 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762302 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3762301 A Prop f x). Qed.
Lemma lem3762304 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3762302 A s x). Qed.
Lemma lem3762305 {A : Type'} (s : A -> Prop) (x : A) : (term638 A s x) = (term926 A s x).
Proof. exact (MK_COMB (@lem3762296) (@lem3762304 A s x)). Qed.
Lemma lem3762306 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762307 {A : Type'} (s : A -> Prop) (x : A) : (term948 A s x) = (term949 A s x).
Proof. exact (MK_COMB (@lem3762306) (@lem3762305 A s x)). Qed.
Lemma lem3762308 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term558 A s t x) = (term950 A s t x).
Proof. exact (MK_COMB (@lem3762307 A s x) (@lem3762295 A t x)). Qed.
Lemma lem3762309 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term559 A s t) = (term951 A s t).
Proof. exact (fun_ext (fun x : A => @lem3762308 A s t x)). Qed.
Lemma lem3762310 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3762311 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term560 A s t) = (term952 A s t).
Proof. exact (MK_COMB (@lem3762310 A) (@lem3762309 A s t)). Qed.
Lemma lem3762312 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762313 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term561 A s t) = (term953 A s t).
Proof. exact (MK_COMB (@lem3762312) (@lem3762311 A s t)). Qed.
Lemma lem3762314 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term562 A t s) = (term954 A t s).
Proof. exact (MK_COMB (@lem3762313 A s t) (@lem3762287 A t s)). Qed.
Lemma lem3762315 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3762320 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762321 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3762320 (A -> Prop) Prop f x). Qed.
Lemma lem3762323 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3762321 A f t). Qed.
Lemma lem3762324 {A : Type'} (f : type686 A) (t : A -> Prop) : (term506 A f t) = (term927 A f t).
Proof. exact (MK_COMB (@lem3762315) (@lem3762323 A f t)). Qed.
Lemma lem3762325 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762326 {A : Type'} (f : type686 A) (t : A -> Prop) : (term563 A f t) = (term928 A f t).
Proof. exact (MK_COMB (@lem3762325) (@lem3762324 A f t)). Qed.
Lemma lem3762327 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term565 A f t s) = (term955 A f t s).
Proof. exact (MK_COMB (@lem3762326 A f t) (@lem3762314 A t s)). Qed.
Lemma lem3762328 {A : Type'} (f : type686 A) (s : A -> Prop) : (term566 A f s) = (term956 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3762327 A f t s)). Qed.
Lemma lem3762329 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3762330 {A : Type'} (f : type686 A) (s : A -> Prop) : (term567 A f s) = (term957 A f s).
Proof. exact (MK_COMB (@lem3762329 A) (@lem3762328 A f s)). Qed.
Lemma lem3762331 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3762336 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3762337 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3762336 (A -> Prop) Prop f x). Qed.
Lemma lem3762339 {A : Type'} (f : type686 A) (s : A -> Prop) : (f s) = (@I ((A -> Prop) -> Prop) f s).
Proof. exact (@lem3762337 A f s). Qed.
Lemma lem3762340 {A : Type'} (f : type686 A) (s : A -> Prop) : (term506 A f s) = (term927 A f s).
Proof. exact (MK_COMB (@lem3762331) (@lem3762339 A f s)). Qed.
Lemma lem3762341 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3762342 {A : Type'} (f : type686 A) (s : A -> Prop) : (term563 A f s) = (term928 A f s).
Proof. exact (MK_COMB (@lem3762341) (@lem3762340 A f s)). Qed.
Lemma lem3762343 {A : Type'} (f : type686 A) (s : A -> Prop) : (term569 A f s) = (term965 A f s).
Proof. exact (MK_COMB (@lem3762342 A f s) (@lem3762330 A f s)). Qed.
Lemma lem3762344 {A : Type'} (f : type686 A) : (term570 A f) = (term966 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3762343 A f s)). Qed.
Lemma lem3762345 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3762346 {A : Type'} (f : type686 A) : (term571 A f) = (term967 A f).
Proof. exact (MK_COMB (@lem3762345 A) (@lem3762344 A f)). Qed.
Lemma lem3762347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3762348 {A : Type'} (f : type686 A) : (term589 A f) = (term968 A f).
Proof. exact (MK_COMB (@lem3762347) (@lem3762346 A f)). Qed.
Lemma lem3762349 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) : (term620 A s f x'') = (term969 A s f x'').
Proof. exact (MK_COMB (@lem3762348 A f) (@lem3762263 A s f x'')). Qed.
Lemma lem3762350 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term969 A s f x''.
Proof. exact (EQ_MP (@lem3762349 A s f x'') (@lem3761892 A s f x'' h1)). Qed.
Lemma lem3762351 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term964 A s f x''.
Proof. exact (proj2 (@lem3762350 A s f x'' h1)). Qed.
Lemma lem3762353 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term959 A s f x''.
Proof. exact (proj2 (@lem3762351 A s f x'' h1)). Qed.
Lemma lem3762356 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term957 A f s.
Proof. exact (proj1 (@lem3762353 A s f x'' h1)). Qed.
Lemma lem3762357 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term914 A t x s f t' x') : term941 A s f t' x'.
Proof. exact (proj2 (@lem3762115 A t x s f t' x' h1)). Qed.
Lemma lem3762358 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term914 A t x s f t' x') : term945 A t f s x.
Proof. exact (proj1 (@lem3762115 A t x s f t' x' h1)). Qed.
Lemma lem3762359 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term939 A s t' f x') : term939 A s t' f x'.
Proof. exact (h1). Qed.
Lemma lem3762360 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term935 A s f t' x'.
Proof. exact (h1). Qed.
Lemma lem3762361 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term939 A s t' f x') : term931 A f x'.
Proof. exact (proj2 (@lem3762359 A s t' f x' h1)). Qed.
Lemma lem3762362 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term939 A s t' f x') : term937 A s f t' x'.
Proof. exact (proj1 (@lem3762359 A s t' f x' h1)). Qed.
Lemma lem3762364 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term925 A f t' x') : term925 A f t' x'.
Proof. exact (h1). Qed.
Lemma lem3762365 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) : term943 A f t s x.
Proof. exact (h1). Qed.
Lemma lem3762366 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term942 A f s x.
Proof. exact (h1). Qed.
Lemma lem3762368 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) : term937 A s f t x.
Proof. exact (proj1 (@lem3762365 A f t s x h1)). Qed.
Lemma lem3762370 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term925 A f t x) : term925 A f t x.
Proof. exact (h1). Qed.
Lemma lem3762374 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term933 A s f x.
Proof. exact (proj1 (@lem3762366 A f s x h1)). Qed.
Lemma lem3762379 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) : term943 A f t s x.
Proof. exact (h1). Qed.
Lemma lem3762380 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term942 A f s x.
Proof. exact (h1). Qed.
Lemma lem3762382 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) : term937 A s f t x.
Proof. exact (proj1 (@lem3762379 A f t s x h1)). Qed.
Lemma lem3762388 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term933 A s f x.
Proof. exact (proj1 (@lem3762380 A f s x h1)). Qed.
Lemma lem3762391 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term925 A f t' x'.
Proof. exact (proj2 (@lem3762360 A s f t' x' h1)). Qed.
Lemma lem3762392 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term933 A s f x'.
Proof. exact (proj1 (@lem3762360 A s f t' x' h1)). Qed.
Lemma lem3762395 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term931 A f x'.
Proof. exact (proj2 (@lem3762392 A s f t' x' h1)). Qed.
Lemma lem3762397 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) : term943 A f t s x.
Proof. exact (h1). Qed.
Lemma lem3762398 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term942 A f s x.
Proof. exact (h1). Qed.
Lemma lem3762400 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) : term937 A s f t x.
Proof. exact (proj1 (@lem3762397 A f t s x h1)). Qed.
Lemma lem3762406 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term933 A s f x.
Proof. exact (proj1 (@lem3762398 A f s x h1)). Qed.
Lemma lem3762922 {A : Type'} (s : A -> Prop) (x : A) (h1 : @I (A -> Prop) s x) : @I (A -> Prop) s x.
Proof. exact (h1). Qed.
Lemma lem3763275 {A : Type'} (P : A -> Prop) (Q : Prop) : (term970 A P Q) = (term971 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3763276 {A : Type'} (P : A -> Prop) (Q : Prop) : (term970 A P Q) = (term971 A P Q).
Proof. exact (@lem3763275 A P Q). Qed.
Lemma lem3763277 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term972 A t s) = (term973 A t s).
Proof. exact (@lem3763276 A (term951 A s t) (term952 A t s)). Qed.
Lemma lem3763278 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term974 A s t x) = (term950 A s t x).
Proof. exact (eq_refl (term974 A s t x)). Qed.
Lemma lem3763279 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term975 A s t) = (term951 A s t).
Proof. exact (fun_ext (fun x : A => @lem3763278 A s t x)). Qed.
Lemma lem3763280 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3763281 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term976 A s t) = (term952 A s t).
Proof. exact (MK_COMB (@lem3763280 A) (@lem3763279 A s t)). Qed.
Lemma lem3763282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3763283 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term977 A s t) = (term953 A s t).
Proof. exact (MK_COMB (@lem3763282) (@lem3763281 A s t)). Qed.
Lemma lem3763284 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term952 A t s) = (term952 A t s).
Proof. exact (eq_refl (term952 A t s)). Qed.
Lemma lem3763285 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term972 A t s) = (term954 A t s).
Proof. exact (MK_COMB (@lem3763283 A s t) (@lem3763284 A t s)). Qed.
Lemma lem3763286 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3763287 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term978 A t s) = (term979 A t s).
Proof. exact (MK_COMB (@lem3763286) (@lem3763285 A t s)). Qed.
Lemma lem3763288 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term974 A s t x) = (term950 A s t x).
Proof. exact (eq_refl (term974 A s t x)). Qed.
Lemma lem3763289 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3763290 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term980 A s t x) = (term981 A s t x).
Proof. exact (MK_COMB (@lem3763289) (@lem3763288 A s t x)). Qed.
Lemma lem3763291 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term952 A t s) = (term952 A t s).
Proof. exact (eq_refl (term952 A t s)). Qed.
Lemma lem3763292 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term982 A x t s) = (term983 A x t s).
Proof. exact (MK_COMB (@lem3763290 A s t x) (@lem3763291 A t s)). Qed.
Lemma lem3763293 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term984 A t s) = (term985 A t s).
Proof. exact (fun_ext (fun x : A => @lem3763292 A x t s)). Qed.
Lemma lem3763294 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3763295 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term973 A t s) = (term986 A t s).
Proof. exact (MK_COMB (@lem3763294 A) (@lem3763293 A t s)). Qed.
Lemma lem3763296 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term972 A t s) = (term973 A t s)) = ((term954 A t s) = (term986 A t s)).
Proof. exact (MK_COMB (@lem3763287 A t s) (@lem3763295 A t s)). Qed.
Lemma lem3763297 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term954 A t s) = (term986 A t s).
Proof. exact (EQ_MP (@lem3763296 A t s) (@lem3763277 A t s)). Qed.
Lemma lem3763299 {A : Type'} (P : Prop) (Q : A -> Prop) : (term987 A P Q) = (term988 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3763300 {A : Type'} (P : Prop) (Q : A -> Prop) : (term987 A P Q) = (term988 A P Q).
Proof. exact (@lem3763299 A P Q). Qed.
Lemma lem3763301 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term989 A x t s) = (term990 A x t s).
Proof. exact (@lem3763300 A (term950 A s t x) (term951 A t s)). Qed.
Lemma lem3763302 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term974 A t s x) = (term950 A t s x).
Proof. exact (eq_refl (term974 A t s x)). Qed.
Lemma lem3763303 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term975 A t s) = (term951 A t s).
Proof. exact (fun_ext (fun x : A => @lem3763302 A t s x)). Qed.
Lemma lem3763304 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3763305 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term976 A t s) = (term952 A t s).
Proof. exact (MK_COMB (@lem3763304 A) (@lem3763303 A t s)). Qed.
Lemma lem3763306 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term981 A s t x) = (term981 A s t x).
Proof. exact (eq_refl (term981 A s t x)). Qed.
Lemma lem3763307 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term989 A x t s) = (term983 A x t s).
Proof. exact (MK_COMB (@lem3763306 A s t x) (@lem3763305 A t s)). Qed.
Lemma lem3763308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3763309 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term991 A x t s) = (term992 A x t s).
Proof. exact (MK_COMB (@lem3763308) (@lem3763307 A x t s)). Qed.
Lemma lem3763310 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) : (term974 A t s x') = (term950 A t s x').
Proof. exact (eq_refl (term974 A t s x')). Qed.
Lemma lem3763311 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term981 A s t x) = (term981 A s t x).
Proof. exact (eq_refl (term981 A s t x)). Qed.
Lemma lem3763312 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term993 A x t s x') = (term994 A x t s x').
Proof. exact (MK_COMB (@lem3763311 A s t x) (@lem3763310 A t s x')). Qed.
Lemma lem3763313 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term995 A x t s) = (term996 A x t s).
Proof. exact (fun_ext (fun x' : A => @lem3763312 A x t s x')). Qed.
Lemma lem3763314 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3763315 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term990 A x t s) = (term997 A x t s).
Proof. exact (MK_COMB (@lem3763314 A) (@lem3763313 A x t s)). Qed.
Lemma lem3763316 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : ((term989 A x t s) = (term990 A x t s)) = ((term983 A x t s) = (term997 A x t s)).
Proof. exact (MK_COMB (@lem3763309 A x t s) (@lem3763315 A x t s)). Qed.
Lemma lem3763317 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term983 A x t s) = (term997 A x t s).
Proof. exact (EQ_MP (@lem3763316 A x t s) (@lem3763301 A x t s)). Qed.
Lemma lem3763318 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term985 A t s) = (term998 A t s).
Proof. exact (fun_ext (fun x : A => @lem3763317 A x t s)). Qed.
Lemma lem3763319 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3763320 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term986 A t s) = (term999 A t s).
Proof. exact (MK_COMB (@lem3763319 A) (@lem3763318 A t s)). Qed.
Lemma lem3763321 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term954 A t s) = (term999 A t s).
Proof. exact (TRANS (@lem3763297 A t s) (@lem3763320 A t s)). Qed.
Lemma lem3763322 {A : Type'} (f : type686 A) (t : A -> Prop) : (term928 A f t) = (term928 A f t).
Proof. exact (eq_refl (term928 A f t)). Qed.
Lemma lem3763323 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term955 A f t s) = (term1000 A f t s).
Proof. exact (MK_COMB (@lem3763322 A f t) (@lem3763321 A t s)). Qed.
Lemma lem3763325 {A : Type'} (P : Prop) (Q : A -> Prop) : (term987 A P Q) = (term988 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3763326 {A : Type'} (P : Prop) (Q : A -> Prop) : (term987 A P Q) = (term988 A P Q).
Proof. exact (@lem3763325 A P Q). Qed.
Lemma lem3763327 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1001 A f t s) = (term1002 A f t s).
Proof. exact (@lem3763326 A (term927 A f t) (term998 A t s)). Qed.
Lemma lem3763328 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term1003 A t s x) = (term997 A x t s).
Proof. exact (eq_refl (term1003 A t s x)). Qed.
Lemma lem3763329 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term1004 A t s) = (term998 A t s).
Proof. exact (fun_ext (fun x : A => @lem3763328 A x t s)). Qed.
Lemma lem3763330 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3763331 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term1005 A t s) = (term999 A t s).
Proof. exact (MK_COMB (@lem3763330 A) (@lem3763329 A t s)). Qed.
Lemma lem3763332 {A : Type'} (f : type686 A) (t : A -> Prop) : (term928 A f t) = (term928 A f t).
Proof. exact (eq_refl (term928 A f t)). Qed.
Lemma lem3763333 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1001 A f t s) = (term1000 A f t s).
Proof. exact (MK_COMB (@lem3763332 A f t) (@lem3763331 A t s)). Qed.
Lemma lem3763334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3763335 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1006 A f t s) = (term1007 A f t s).
Proof. exact (MK_COMB (@lem3763334) (@lem3763333 A f t s)). Qed.
Lemma lem3763336 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term1003 A t s x) = (term997 A x t s).
Proof. exact (eq_refl (term1003 A t s x)). Qed.
Lemma lem3763337 {A : Type'} (f : type686 A) (t : A -> Prop) : (term928 A f t) = (term928 A f t).
Proof. exact (eq_refl (term928 A f t)). Qed.
Lemma lem3763338 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1008 A f t s x) = (term1009 A f x t s).
Proof. exact (MK_COMB (@lem3763337 A f t) (@lem3763336 A x t s)). Qed.
Lemma lem3763339 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1010 A f t s) = (term1011 A f t s).
Proof. exact (fun_ext (fun x : A => @lem3763338 A f x t s)). Qed.
Lemma lem3763340 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3763341 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1002 A f t s) = (term1012 A f t s).
Proof. exact (MK_COMB (@lem3763340 A) (@lem3763339 A f t s)). Qed.
Lemma lem3763342 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : ((term1001 A f t s) = (term1002 A f t s)) = ((term1000 A f t s) = (term1012 A f t s)).
Proof. exact (MK_COMB (@lem3763335 A f t s) (@lem3763341 A f t s)). Qed.
Lemma lem3763343 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1000 A f t s) = (term1012 A f t s).
Proof. exact (EQ_MP (@lem3763342 A f t s) (@lem3763327 A f t s)). Qed.
Lemma lem3763345 {A : Type'} (P : Prop) (Q : A -> Prop) : (term987 A P Q) = (term988 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3763346 {A : Type'} (P : Prop) (Q : A -> Prop) : (term987 A P Q) = (term988 A P Q).
Proof. exact (@lem3763345 A P Q). Qed.
Lemma lem3763347 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1013 A f x t s) = (term1014 A f x t s).
Proof. exact (@lem3763346 A (term927 A f t) (term996 A x t s)). Qed.
Lemma lem3763348 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term1015 A x t s x') = (term994 A x t s x').
Proof. exact (eq_refl (term1015 A x t s x')). Qed.
Lemma lem3763349 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term1016 A x t s) = (term996 A x t s).
Proof. exact (fun_ext (fun x' : A => @lem3763348 A x t s x')). Qed.
Lemma lem3763350 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3763351 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term1017 A x t s) = (term997 A x t s).
Proof. exact (MK_COMB (@lem3763350 A) (@lem3763349 A x t s)). Qed.
Lemma lem3763352 {A : Type'} (f : type686 A) (t : A -> Prop) : (term928 A f t) = (term928 A f t).
Proof. exact (eq_refl (term928 A f t)). Qed.
Lemma lem3763353 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1013 A f x t s) = (term1009 A f x t s).
Proof. exact (MK_COMB (@lem3763352 A f t) (@lem3763351 A x t s)). Qed.
Lemma lem3763354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3763355 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1018 A f x t s) = (term1019 A f x t s).
Proof. exact (MK_COMB (@lem3763354) (@lem3763353 A f x t s)). Qed.
Lemma lem3763356 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term1015 A x t s x') = (term994 A x t s x').
Proof. exact (eq_refl (term1015 A x t s x')). Qed.
Lemma lem3763357 {A : Type'} (f : type686 A) (t : A -> Prop) : (term928 A f t) = (term928 A f t).
Proof. exact (eq_refl (term928 A f t)). Qed.
Lemma lem3763358 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term1020 A f x t s x') = (term1021 A f x t s x').
Proof. exact (MK_COMB (@lem3763357 A f t) (@lem3763356 A x t s x')). Qed.
Lemma lem3763359 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1022 A f x t s) = (term1023 A f x t s).
Proof. exact (fun_ext (fun x' : A => @lem3763358 A f x t s x')). Qed.
Lemma lem3763360 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3763361 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1014 A f x t s) = (term1024 A f x t s).
Proof. exact (MK_COMB (@lem3763360 A) (@lem3763359 A f x t s)). Qed.
Lemma lem3763362 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : ((term1013 A f x t s) = (term1014 A f x t s)) = ((term1009 A f x t s) = (term1024 A f x t s)).
Proof. exact (MK_COMB (@lem3763355 A f x t s) (@lem3763361 A f x t s)). Qed.
Lemma lem3763363 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1009 A f x t s) = (term1024 A f x t s).
Proof. exact (EQ_MP (@lem3763362 A f x t s) (@lem3763347 A f x t s)). Qed.
Lemma lem3763364 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1011 A f t s) = (term1025 A f t s).
Proof. exact (fun_ext (fun x : A => @lem3763363 A f x t s)). Qed.
Lemma lem3763365 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3763366 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1012 A f t s) = (term1026 A f t s).
Proof. exact (MK_COMB (@lem3763365 A) (@lem3763364 A f t s)). Qed.
Lemma lem3763367 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1000 A f t s) = (term1026 A f t s).
Proof. exact (TRANS (@lem3763343 A f t s) (@lem3763366 A f t s)). Qed.
Lemma lem3763368 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term955 A f t s) = (term1026 A f t s).
Proof. exact (TRANS (@lem3763323 A f t s) (@lem3763367 A f t s)). Qed.
Lemma lem3763369 {A : Type'} (f : type686 A) (s : A -> Prop) : (term956 A f s) = (term1027 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3763368 A f t s)). Qed.
Lemma lem3763370 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3763371 {A : Type'} (f : type686 A) (s : A -> Prop) : (term957 A f s) = (term1028 A f s).
Proof. exact (MK_COMB (@lem3763370 A) (@lem3763369 A f s)). Qed.
Lemma lem3763396 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term1021 A f x t s x') = (term1021 A f x t s x').
Proof. exact (eq_refl (term1021 A f x t s x')). Qed.
Lemma lem3763397 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1023 A f x t s) = (term1023 A f x t s).
Proof. exact (fun_ext (fun x' : A => @lem3763396 A f x t s x')). Qed.
Lemma lem3763398 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3763399 {A : Type'} (f : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term1024 A f x t s) = (term1024 A f x t s).
Proof. exact (MK_COMB (@lem3763398 A) (@lem3763397 A f x t s)). Qed.
Lemma lem3763400 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1025 A f t s) = (term1025 A f t s).
Proof. exact (fun_ext (fun x : A => @lem3763399 A f x t s)). Qed.
Lemma lem3763401 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3763402 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) : (term1026 A f t s) = (term1026 A f t s).
Proof. exact (MK_COMB (@lem3763401 A) (@lem3763400 A f t s)). Qed.
Lemma lem3763403 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1027 A f s) = (term1027 A f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3763402 A f t s)). Qed.
Lemma lem3763404 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3763405 {A : Type'} (f : type686 A) (s : A -> Prop) : (term1028 A f s) = (term1028 A f s).
Proof. exact (MK_COMB (@lem3763404 A) (@lem3763403 A f s)). Qed.
Lemma lem3763406 {A : Type'} (f : type686 A) (s : A -> Prop) : (term957 A f s) = (term1028 A f s).
Proof. exact (TRANS (@lem3763371 A f s) (@lem3763405 A f s)). Qed.
Lemma lem3763407 {A : Type'} (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term1028 A f s.
Proof. exact (EQ_MP (@lem3763406 A f s) (@lem3762356 A s f x'' h1)). Qed.
Lemma lem3763419 {A : Type'} (f : type686 A) (t : A -> Prop) (x' : A) : (term929 A f t x') = (term929 A f t x').
Proof. exact (eq_refl (term929 A f t x')). Qed.
Lemma lem3763420 {A : Type'} (f : type686 A) (x' : A) : (term930 A f x') = (term930 A f x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3763419 A f t x')). Qed.
Lemma lem3763421 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3763423 {A : Type'} (f : type686 A) (x' : A) : (term931 A f x') = (term931 A f x').
Proof. exact (MK_COMB (@lem3763421 A) (@lem3763420 A f x')). Qed.
Lemma lem3763424 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term939 A s t' f x') : term931 A f x'.
Proof. exact (EQ_MP (@lem3763423 A f x') (@lem3762361 A s t' f x' h1)). Qed.
Lemma lem3763428 {A : Type'} (s : A -> Prop) (x' : A) (h1 : @I (A -> Prop) s x') : @I (A -> Prop) s x'.
Proof. exact (h1). Qed.
Lemma lem3764485 {A : Type'} (s : A -> Prop) (x : A) (h1 : @I (A -> Prop) s x) : @I (A -> Prop) s x.
Proof. exact (h1). Qed.
Lemma lem3764982 {A : Type'} (f : type686 A) (t : A -> Prop) (x' : A) : (term929 A f t x') = (term929 A f t x').
Proof. exact (eq_refl (term929 A f t x')). Qed.
Lemma lem3764983 {A : Type'} (f : type686 A) (x' : A) : (term930 A f x') = (term930 A f x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3764982 A f t x')). Qed.
Lemma lem3764984 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3764986 {A : Type'} (f : type686 A) (x' : A) : (term931 A f x') = (term931 A f x').
Proof. exact (MK_COMB (@lem3764984 A) (@lem3764983 A f x')). Qed.
Lemma lem3764987 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term939 A s t' f x') : term931 A f x'.
Proof. exact (EQ_MP (@lem3764986 A f x') (@lem3762361 A s t' f x' h1)). Qed.
Lemma lem3766060 {A : Type'} (s : A -> Prop) (x : A) (h1 : @I (A -> Prop) s x) : @I (A -> Prop) s x.
Proof. exact (h1). Qed.
Lemma lem3766569 {A : Type'} (f : type686 A) (t : A -> Prop) (x' : A) : (term929 A f t x') = (term929 A f t x').
Proof. exact (eq_refl (term929 A f t x')). Qed.
Lemma lem3766570 {A : Type'} (f : type686 A) (x' : A) : (term930 A f x') = (term930 A f x').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3766569 A f t x')). Qed.
Lemma lem3766571 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3766573 {A : Type'} (f : type686 A) (x' : A) : (term931 A f x') = (term931 A f x').
Proof. exact (MK_COMB (@lem3766571 A) (@lem3766570 A f x')). Qed.
Lemma lem3766574 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term931 A f x'.
Proof. exact (EQ_MP (@lem3766573 A f x') (@lem3762395 A s f t' x' h1)). Qed.
Lemma lem3767176 {A : Type'} (_43241 : A -> Prop) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term1029 A f s _43241.
Proof. exact (@lem3763407 A s f x'' h1 _43241). Qed.
Lemma lem3767177 {A : Type'} (f : type686 A) (_43241 : A -> Prop) (s : A -> Prop) : (term1029 A f s _43241) = (term1026 A f _43241 s).
Proof. exact (eq_refl (term1029 A f s _43241)). Qed.
Lemma lem3767178 {A : Type'} (_43241 : A -> Prop) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term1026 A f _43241 s.
Proof. exact (EQ_MP (@lem3767177 A f _43241 s) (@lem3767176 A _43241 s f x'' h1)). Qed.
Lemma lem3767179 {A : Type'} (_43241 : A -> Prop) (_43242 : A) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term1030 A f _43241 s _43242.
Proof. exact (@lem3767178 A _43241 s f x'' h1 _43242). Qed.
Lemma lem3767180 {A : Type'} (f : type686 A) (_43242 : A) (_43241 : A -> Prop) (s : A -> Prop) : (term1030 A f _43241 s _43242) = (term1024 A f _43242 _43241 s).
Proof. exact (eq_refl (term1030 A f _43241 s _43242)). Qed.
Lemma lem3767181 {A : Type'} (_43242 : A) (_43241 : A -> Prop) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term1024 A f _43242 _43241 s.
Proof. exact (EQ_MP (@lem3767180 A f _43242 _43241 s) (@lem3767179 A _43241 _43242 s f x'' h1)). Qed.
Lemma lem3767182 {A : Type'} (_43242 : A) (_43241 : A -> Prop) (_43243 : A) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term1031 A f _43242 _43241 s _43243.
Proof. exact (@lem3767181 A _43242 _43241 s f x'' h1 _43243). Qed.
Lemma lem3767183 {A : Type'} (f : type686 A) (_43242 : A) (_43241 : A -> Prop) (s : A -> Prop) (_43243 : A) : (term1031 A f _43242 _43241 s _43243) = (term1021 A f _43242 _43241 s _43243).
Proof. exact (eq_refl (term1031 A f _43242 _43241 s _43243)). Qed.
Lemma lem3767184 {A : Type'} (_43242 : A) (_43241 : A -> Prop) (_43243 : A) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term1021 A f _43242 _43241 s _43243.
Proof. exact (EQ_MP (@lem3767183 A f _43242 _43241 s _43243) (@lem3767182 A _43242 _43241 _43243 s f x'' h1)). Qed.
Lemma lem3767185 {A : Type'} (_43244 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term939 A s t' f x') : term1032 A f x' _43244.
Proof. exact (@lem3763424 A s t' f x' h1 _43244). Qed.
Lemma lem3767186 {A : Type'} (f : type686 A) (_43244 : A -> Prop) (x' : A) : (term1032 A f x' _43244) = (term929 A f _43244 x').
Proof. exact (eq_refl (term1032 A f x' _43244)). Qed.
Lemma lem3767287 {A : Type'} (_43278 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term939 A s t' f x') : term1032 A f x' _43278.
Proof. exact (@lem3764987 A s t' f x' h1 _43278). Qed.
Lemma lem3767288 {A : Type'} (f : type686 A) (_43278 : A -> Prop) (x' : A) : (term1032 A f x' _43278) = (term929 A f _43278 x').
Proof. exact (eq_refl (term1032 A f x' _43278)). Qed.
Lemma lem3767389 {A : Type'} (_43312 : A -> Prop) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term1032 A f x' _43312.
Proof. exact (@lem3766574 A s f t' x' h1 _43312). Qed.
Lemma lem3767390 {A : Type'} (f : type686 A) (_43312 : A -> Prop) (x' : A) : (term1032 A f x' _43312) = (term929 A f _43312 x').
Proof. exact (eq_refl (term1032 A f x' _43312)). Qed.
Lemma lem3767503 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) : term926 A s x.
Proof. exact (proj2 (@lem3762365 A f t s x h1)). Qed.
Lemma lem3767505 {A : Type'} (s : A -> Prop) (x : A) (h1 : @I (A -> Prop) s x) : @I (A -> Prop) s x.
Proof. exact (h1). Qed.
Lemma lem3767564 {A : Type'} (_43242 : A) (_43241 : A -> Prop) (s : A -> Prop) (_43243 : A) : (term994 A _43242 _43241 s _43243) = (term1033 A _43242 _43241 s _43243).
Proof. exact (@lem3759035 (term926 A s _43242) (@I (A -> Prop) _43241 _43242) (term950 A _43241 s _43243)). Qed.
Lemma lem3767565 {A : Type'} (f : type686 A) (_43241 : A -> Prop) : (term928 A f _43241) = (term928 A f _43241).
Proof. exact (eq_refl (term928 A f _43241)). Qed.
Lemma lem3767568 {A : Type'} (f : type686 A) (_43242 : A) (_43241 : A -> Prop) (s : A -> Prop) (_43243 : A) : (term1021 A f _43242 _43241 s _43243) = (term1034 A f _43242 _43241 s _43243).
Proof. exact (MK_COMB (@lem3767565 A f _43241) (@lem3767564 A _43242 _43241 s _43243)). Qed.
Lemma lem3767569 {A : Type'} (_43242 : A) (_43241 : A -> Prop) (_43243 : A) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term1034 A f _43242 _43241 s _43243.
Proof. exact (EQ_MP (@lem3767568 A f _43242 _43241 s _43243) (@lem3767184 A _43242 _43241 _43243 s f x'' h1)). Qed.
Lemma lem3767577 {A : Type'} (_43244 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term939 A s t' f x') : term929 A f _43244 x'.
Proof. exact (EQ_MP (@lem3767186 A f _43244 x') (@lem3767185 A _43244 s t' f x' h1)). Qed.
Lemma lem3767579 {A : Type'} (s : A -> Prop) (x' : A) (h1 : @I (A -> Prop) s x') : @I (A -> Prop) s x'.
Proof. exact (h1). Qed.
Lemma lem3767581 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) : term926 A s x.
Proof. exact (proj2 (@lem3762365 A f t s x h1)). Qed.
Lemma lem3767663 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term926 A s x.
Proof. exact (proj1 (@lem3762374 A f s x h1)). Qed.
Lemma lem3767747 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) : term926 A s x.
Proof. exact (proj2 (@lem3762379 A f t s x h1)). Qed.
Lemma lem3767749 {A : Type'} (s : A -> Prop) (x : A) (h1 : @I (A -> Prop) s x) : @I (A -> Prop) s x.
Proof. exact (h1). Qed.
Lemma lem3767821 {A : Type'} (_43278 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term939 A s t' f x') : term929 A f _43278 x'.
Proof. exact (EQ_MP (@lem3767288 A f _43278 x') (@lem3767287 A _43278 s t' f x' h1)). Qed.
Lemma lem3767911 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term926 A s x.
Proof. exact (proj1 (@lem3762388 A f s x h1)). Qed.
Lemma lem3767997 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) : term926 A s x.
Proof. exact (proj2 (@lem3762397 A f t s x h1)). Qed.
Lemma lem3767999 {A : Type'} (s : A -> Prop) (x : A) (h1 : @I (A -> Prop) s x) : @I (A -> Prop) s x.
Proof. exact (h1). Qed.
Lemma lem3768077 {A : Type'} (_43312 : A -> Prop) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term929 A f _43312 x'.
Proof. exact (EQ_MP (@lem3767390 A f _43312 x') (@lem3767389 A _43312 s f t' x' h1)). Qed.
Lemma lem3768165 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term926 A s x.
Proof. exact (proj1 (@lem3762406 A f s x h1)). Qed.
Lemma lem3768173 {A : Type'} (s : A -> Prop) (x : A) (h1 : @I (A -> Prop) s x) : @I (A -> Prop) s x.
Proof. exact (h1). Qed.
Lemma lem3768174 {A : Type'} (s : A -> Prop) (x : A) (h1 : @I (A -> Prop) s x) : term1035 A s x.
Proof. exact (fun h0 : term926 A s x => @lem3768173 A s x h1). Qed.
Lemma lem3768176 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768177 {A : Type'} (s : A -> Prop) (x : A) : (term1035 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3768176 (@I (A -> Prop) s x)). Qed.
Lemma lem3768178 {A : Type'} (s : A -> Prop) (x : A) (h1 : @I (A -> Prop) s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3768177 A s x) (@lem3768174 A s x h1)). Qed.
Lemma lem3768181 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3768183 {A : Type'} (s : A -> Prop) (x : A) : (term926 A s x) = (term1036 A s x).
Proof. exact (@lem3768181 (@I (A -> Prop) s x)). Qed.
Lemma lem3768186 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) : term1036 A s x.
Proof. exact (EQ_MP (@lem3768183 A s x) (@lem3767503 A f t s x h1)). Qed.
Lemma lem3768189 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : False.
Proof. exact (@lem3768186 A f t s x h1 (@lem3768178 A s x h2)). Qed.
Lemma lem3768190 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : term32.
Proof. exact (fun h0 : ~ False => @lem3768189 A f t s x h1 h2). Qed.
Lemma lem3768192 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768193 : term32 = False.
Proof. exact (@lem3768192 False). Qed.
Lemma lem3768194 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3768193) (@lem3768190 A f t s x h1 h2)). Qed.
Lemma lem3768196 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term925 A f t x) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem3762370 A f t x h1)). Qed.
Lemma lem3768197 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term925 A f t x) : term1037 A f t.
Proof. exact (fun h0 : term927 A f t => @lem3768196 A f t x h1). Qed.
Lemma lem3768199 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768200 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1037 A f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3768199 (@I ((A -> Prop) -> Prop) f t)). Qed.
Lemma lem3768201 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term925 A f t x) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem3768200 A f t) (@lem3768197 A f t x h1)). Qed.
Lemma lem3768203 {A : Type'} (s : A -> Prop) (x' : A) (h1 : @I (A -> Prop) s x') : @I (A -> Prop) s x'.
Proof. exact (h1). Qed.
Lemma lem3768204 {A : Type'} (s : A -> Prop) (x' : A) (h1 : @I (A -> Prop) s x') : term1035 A s x'.
Proof. exact (fun h0 : term926 A s x' => @lem3768203 A s x' h1). Qed.
Lemma lem3768206 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768207 {A : Type'} (s : A -> Prop) (x' : A) : (term1035 A s x') = (@I (A -> Prop) s x').
Proof. exact (@lem3768206 (@I (A -> Prop) s x')). Qed.
Lemma lem3768208 {A : Type'} (s : A -> Prop) (x' : A) (h1 : @I (A -> Prop) s x') : @I (A -> Prop) s x'.
Proof. exact (EQ_MP (@lem3768207 A s x') (@lem3768204 A s x' h1)). Qed.
Lemma lem3768210 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term925 A f t x) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem3762370 A f t x h1)). Qed.
Lemma lem3768211 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term925 A f t x) : term1037 A f t.
Proof. exact (fun h0 : term927 A f t => @lem3768210 A f t x h1). Qed.
Lemma lem3768213 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768214 {A : Type'} (f : type686 A) (t : A -> Prop) : (term1037 A f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3768213 (@I ((A -> Prop) -> Prop) f t)). Qed.
Lemma lem3768215 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term925 A f t x) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem3768214 A f t) (@lem3768211 A f t x h1)). Qed.
Lemma lem3768221 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3768222 {A : Type'} (x' : A) (f : type686 A) (_43244 : A -> Prop) : (term929 A f _43244 x') = (term1038 A x' f _43244).
Proof. exact (@lem3768221 (term926 A _43244 x') (term927 A f _43244)). Qed.
Lemma lem3768228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3768229 {A : Type'} (x' : A) (f : type686 A) (_43244 : A -> Prop) : (term1039 A f _43244 x') = (term1040 A x' f _43244).
Proof. exact (MK_COMB (@lem3768228) (@lem3768222 A x' f _43244)). Qed.
Lemma lem3768235 {A : Type'} (x' : A) (f : type686 A) (_43244 : A -> Prop) : (term1038 A x' f _43244) = (term1038 A x' f _43244).
Proof. exact (eq_refl (term1038 A x' f _43244)). Qed.
Lemma lem3768236 {A : Type'} (x' : A) (f : type686 A) (_43244 : A -> Prop) : ((term929 A f _43244 x') = (term1038 A x' f _43244)) = ((term1038 A x' f _43244) = (term1038 A x' f _43244)).
Proof. exact (MK_COMB (@lem3768229 A x' f _43244) (@lem3768235 A x' f _43244)). Qed.
Lemma lem3768238 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3768239 (x : Prop) : (x = x) = True.
Proof. exact (@lem3768238 Prop x). Qed.
Lemma lem3768240 {A : Type'} (x' : A) (f : type686 A) (_43244 : A -> Prop) : ((term1038 A x' f _43244) = (term1038 A x' f _43244)) = True.
Proof. exact (@lem3768239 (term1038 A x' f _43244)). Qed.
Lemma lem3768241 {A : Type'} (x' : A) (f : type686 A) (_43244 : A -> Prop) : ((term929 A f _43244 x') = (term1038 A x' f _43244)) = True.
Proof. exact (TRANS (@lem3768236 A x' f _43244) (@lem3768240 A x' f _43244)). Qed.
Lemma lem3768242 {A : Type'} (x' : A) (f : type686 A) (_43244 : A -> Prop) : True = ((term929 A f _43244 x') = (term1038 A x' f _43244)).
Proof. exact (SYM (@lem3768241 A x' f _43244)). Qed.
Lemma lem3768243 {A : Type'} (x' : A) (f : type686 A) (_43244 : A -> Prop) : (term929 A f _43244 x') = (term1038 A x' f _43244).
Proof. exact (EQ_MP (@lem3768242 A x' f _43244) (@lem0)). Qed.
Lemma lem3768244 {A : Type'} (_43244 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term939 A s t' f x') : term1038 A x' f _43244.
Proof. exact (EQ_MP (@lem3768243 A x' f _43244) (@lem3767577 A _43244 s t' f x' h1)). Qed.
Lemma lem3768246 (b : Prop) (a : Prop) : (a \/ b) = (term55 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3768247 {A : Type'} (f : type686 A) (_43244 : A -> Prop) (x' : A) : (term1038 A x' f _43244) = (term1041 A f _43244 x').
Proof. exact (@lem3768246 (term927 A f _43244) (term926 A _43244 x')). Qed.
Lemma lem3768249 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3768250 {A : Type'} (f : type686 A) (_43244 : A -> Prop) : (term1042 A f _43244) = (@I ((A -> Prop) -> Prop) f _43244).
Proof. exact (@lem3768249 (@I ((A -> Prop) -> Prop) f _43244)). Qed.
Lemma lem3768251 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3768252 {A : Type'} (f : type686 A) (_43244 : A -> Prop) : (term1043 A f _43244) = (term1044 A f _43244).
Proof. exact (MK_COMB (@lem3768251) (@lem3768250 A f _43244)). Qed.
Lemma lem3768253 {A : Type'} (_43244 : A -> Prop) (x' : A) : (term926 A _43244 x') = (term926 A _43244 x').
Proof. exact (eq_refl (term926 A _43244 x')). Qed.
Lemma lem3768254 {A : Type'} (f : type686 A) (_43244 : A -> Prop) (x' : A) : (term1041 A f _43244 x') = (term1045 A f _43244 x').
Proof. exact (MK_COMB (@lem3768252 A f _43244) (@lem3768253 A _43244 x')). Qed.
Lemma lem3768255 {A : Type'} (f : type686 A) (_43244 : A -> Prop) (x' : A) : (term1038 A x' f _43244) = (term1045 A f _43244 x').
Proof. exact (TRANS (@lem3768247 A f _43244 x') (@lem3768254 A f _43244 x')). Qed.
Lemma lem3768258 {A : Type'} (_43244 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term939 A s t' f x') : term1045 A f _43244 x'.
Proof. exact (EQ_MP (@lem3768255 A f _43244 x') (@lem3768244 A _43244 s t' f x' h1)). Qed.
Lemma lem3768259 {A : Type'} (_43244 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term939 A s t' f x') : term1045 A f _43244 x'.
Proof. exact (@lem3768258 A _43244 s t' f x' h1). Qed.
Lemma lem3768260 {A : Type'} (t : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term939 A s t' f x') : term1045 A f t x'.
Proof. exact (@lem3768259 A t s t' f x' h1). Qed.
Lemma lem3768263 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term925 A f t x) (h2 : term939 A s t' f x') : term926 A t x'.
Proof. exact (@lem3768260 A t s t' f x' h2 (@lem3768215 A f t x h1)). Qed.
Lemma lem3768264 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term925 A f t x) (h2 : term939 A s t' f x') : term1046 A t x'.
Proof. exact (fun h0 : @I (A -> Prop) t x' => @lem3768263 A t x s t' f x' h1 h2). Qed.
Lemma lem3768266 (p : Prop) : (term1047 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3768267 {A : Type'} (t : A -> Prop) (x' : A) : (term1046 A t x') = (term926 A t x').
Proof. exact (@lem3768266 (@I (A -> Prop) t x')). Qed.
Lemma lem3768268 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term925 A f t x) (h2 : term939 A s t' f x') : term926 A t x'.
Proof. exact (EQ_MP (@lem3768267 A t x') (@lem3768264 A t x s t' f x' h1 h2)). Qed.
Lemma lem3768270 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term925 A f t x) : @I (A -> Prop) t x.
Proof. exact (proj2 (@lem3762370 A f t x h1)). Qed.
Lemma lem3768271 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term925 A f t x) : term1035 A t x.
Proof. exact (fun h0 : term926 A t x => @lem3768270 A f t x h1). Qed.
Lemma lem3768273 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768274 {A : Type'} (t : A -> Prop) (x : A) : (term1035 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3768273 (@I (A -> Prop) t x)). Qed.
Lemma lem3768275 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) (h1 : term925 A f t x) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem3768274 A t x) (@lem3768271 A f t x h1)). Qed.
Lemma lem3768281 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3768282 {A : Type'} (f : type686 A) (_43242 : A) (_43241 : A -> Prop) (s : A -> Prop) (_43243 : A) : (term1034 A f _43242 _43241 s _43243) = (term1048 A f _43242 _43241 s _43243).
Proof. exact (@lem3768281 (term926 A s _43242) (term927 A f _43241) (term1049 A _43242 _43241 s _43243)). Qed.
Lemma lem3768296 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3768297 {A : Type'} (_43242 : A) (f : type686 A) (_43241 : A -> Prop) (s : A -> Prop) (_43243 : A) : (term1050 A f _43242 _43241 s _43243) = (term1051 A _43242 f _43241 s _43243).
Proof. exact (@lem3768296 (@I (A -> Prop) _43241 _43242) (term927 A f _43241) (term950 A _43241 s _43243)). Qed.
Lemma lem3768311 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3768312 {A : Type'} (f : type686 A) (_43241 : A -> Prop) (s : A -> Prop) (_43243 : A) : (term1052 A f _43241 s _43243) = (term1053 A f _43241 s _43243).
Proof. exact (@lem3768311 (term926 A _43241 _43243) (term927 A f _43241) (@I (A -> Prop) s _43243)). Qed.
Lemma lem3768326 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3768327 {A : Type'} (s : A -> Prop) (_43243 : A) (f : type686 A) (_43241 : A -> Prop) : (term1054 A f _43241 s _43243) = (term1055 A s _43243 f _43241).
Proof. exact (@lem3768326 (@I (A -> Prop) s _43243) (term927 A f _43241)). Qed.
Lemma lem3768333 {A : Type'} (_43241 : A -> Prop) (_43243 : A) : (term949 A _43241 _43243) = (term949 A _43241 _43243).
Proof. exact (eq_refl (term949 A _43241 _43243)). Qed.
Lemma lem3768334 {A : Type'} (s : A -> Prop) (_43243 : A) (f : type686 A) (_43241 : A -> Prop) : (term1053 A f _43241 s _43243) = (term1056 A s _43243 f _43241).
Proof. exact (MK_COMB (@lem3768333 A _43241 _43243) (@lem3768327 A s _43243 f _43241)). Qed.
Lemma lem3768338 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3768339 {A : Type'} (s : A -> Prop) (_43243 : A) (f : type686 A) (_43241 : A -> Prop) : (term1056 A s _43243 f _43241) = (term1057 A s _43243 f _43241).
Proof. exact (@lem3768338 (@I (A -> Prop) s _43243) (term926 A _43241 _43243) (term927 A f _43241)). Qed.
Lemma lem3768355 {A : Type'} (s : A -> Prop) (_43243 : A) (f : type686 A) (_43241 : A -> Prop) : (term1053 A f _43241 s _43243) = (term1057 A s _43243 f _43241).
Proof. exact (TRANS (@lem3768334 A s _43243 f _43241) (@lem3768339 A s _43243 f _43241)). Qed.
Lemma lem3768356 {A : Type'} (s : A -> Prop) (_43243 : A) (f : type686 A) (_43241 : A -> Prop) : (term1052 A f _43241 s _43243) = (term1057 A s _43243 f _43241).
Proof. exact (TRANS (@lem3768312 A f _43241 s _43243) (@lem3768355 A s _43243 f _43241)). Qed.
Lemma lem3768357 {A : Type'} (_43241 : A -> Prop) (_43242 : A) : (term936 A _43241 _43242) = (term936 A _43241 _43242).
Proof. exact (eq_refl (term936 A _43241 _43242)). Qed.
Lemma lem3768358 {A : Type'} (_43242 : A) (s : A -> Prop) (_43243 : A) (f : type686 A) (_43241 : A -> Prop) : (term1051 A _43242 f _43241 s _43243) = (term1058 A _43242 s _43243 f _43241).
Proof. exact (MK_COMB (@lem3768357 A _43241 _43242) (@lem3768356 A s _43243 f _43241)). Qed.
Lemma lem3768369 {A : Type'} (_43242 : A) (s : A -> Prop) (_43243 : A) (f : type686 A) (_43241 : A -> Prop) : (term1050 A f _43242 _43241 s _43243) = (term1058 A _43242 s _43243 f _43241).
Proof. exact (TRANS (@lem3768297 A _43242 f _43241 s _43243) (@lem3768358 A _43242 s _43243 f _43241)). Qed.
Lemma lem3768370 {A : Type'} (s : A -> Prop) (_43242 : A) : (term949 A s _43242) = (term949 A s _43242).
Proof. exact (eq_refl (term949 A s _43242)). Qed.
Lemma lem3768371 {A : Type'} (_43242 : A) (s : A -> Prop) (_43243 : A) (f : type686 A) (_43241 : A -> Prop) : (term1048 A f _43242 _43241 s _43243) = (term1059 A _43242 s _43243 f _43241).
Proof. exact (MK_COMB (@lem3768370 A s _43242) (@lem3768369 A _43242 s _43243 f _43241)). Qed.
Lemma lem3768375 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3768376 {A : Type'} (_43242 : A) (s : A -> Prop) (_43243 : A) (f : type686 A) (_43241 : A -> Prop) : (term1059 A _43242 s _43243 f _43241) = (term1060 A _43242 s _43243 f _43241).
Proof. exact (@lem3768375 (@I (A -> Prop) _43241 _43242) (term926 A s _43242) (term1057 A s _43243 f _43241)). Qed.
Lemma lem3768390 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3768391 {A : Type'} (s : A -> Prop) (_43242 : A) (_43243 : A) (f : type686 A) (_43241 : A -> Prop) : (term1061 A _43242 s _43243 f _43241) = (term1062 A s _43242 _43243 f _43241).
Proof. exact (@lem3768390 (@I (A -> Prop) s _43243) (term926 A s _43242) (term1038 A _43243 f _43241)). Qed.
Lemma lem3768405 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3768406 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : (term1063 A s _43242 _43243 f _43241) = (term1064 A _43243 s _43242 f _43241).
Proof. exact (@lem3768405 (term926 A _43241 _43243) (term926 A s _43242) (term927 A f _43241)). Qed.
Lemma lem3768422 {A : Type'} (s : A -> Prop) (_43243 : A) : (term936 A s _43243) = (term936 A s _43243).
Proof. exact (eq_refl (term936 A s _43243)). Qed.
Lemma lem3768423 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : (term1062 A s _43242 _43243 f _43241) = (term1065 A _43243 s _43242 f _43241).
Proof. exact (MK_COMB (@lem3768422 A s _43243) (@lem3768406 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768434 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : (term1061 A _43242 s _43243 f _43241) = (term1065 A _43243 s _43242 f _43241).
Proof. exact (TRANS (@lem3768391 A s _43242 _43243 f _43241) (@lem3768423 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768435 {A : Type'} (_43241 : A -> Prop) (_43242 : A) : (term936 A _43241 _43242) = (term936 A _43241 _43242).
Proof. exact (eq_refl (term936 A _43241 _43242)). Qed.
Lemma lem3768436 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : (term1060 A _43242 s _43243 f _43241) = (term1066 A _43243 s _43242 f _43241).
Proof. exact (MK_COMB (@lem3768435 A _43241 _43242) (@lem3768434 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768447 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : (term1059 A _43242 s _43243 f _43241) = (term1066 A _43243 s _43242 f _43241).
Proof. exact (TRANS (@lem3768376 A _43242 s _43243 f _43241) (@lem3768436 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768448 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : (term1048 A f _43242 _43241 s _43243) = (term1066 A _43243 s _43242 f _43241).
Proof. exact (TRANS (@lem3768371 A _43242 s _43243 f _43241) (@lem3768447 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768449 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : (term1034 A f _43242 _43241 s _43243) = (term1066 A _43243 s _43242 f _43241).
Proof. exact (TRANS (@lem3768282 A f _43242 _43241 s _43243) (@lem3768448 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768450 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3768451 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : (term1067 A f _43242 _43241 s _43243) = (term1068 A _43243 s _43242 f _43241).
Proof. exact (MK_COMB (@lem3768450) (@lem3768449 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768465 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3768466 {A : Type'} (s : A -> Prop) (f : type686 A) (_43242 : A) (_43241 : A -> Prop) (_43243 : A) : (term1069 A f s _43242 _43241 _43243) = (term1070 A s f _43242 _43241 _43243).
Proof. exact (@lem3768465 (term926 A s _43242) (term927 A f _43241) (term1071 A _43242 _43241 _43243)). Qed.
Lemma lem3768480 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3768481 {A : Type'} (_43242 : A) (f : type686 A) (_43241 : A -> Prop) (_43243 : A) : (term1072 A f _43242 _43241 _43243) = (term1073 A _43242 f _43241 _43243).
Proof. exact (@lem3768480 (@I (A -> Prop) _43241 _43242) (term927 A f _43241) (term926 A _43241 _43243)). Qed.
Lemma lem3768495 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3768496 {A : Type'} (_43243 : A) (f : type686 A) (_43241 : A -> Prop) : (term929 A f _43241 _43243) = (term1038 A _43243 f _43241).
Proof. exact (@lem3768495 (term926 A _43241 _43243) (term927 A f _43241)). Qed.
Lemma lem3768502 {A : Type'} (_43241 : A -> Prop) (_43242 : A) : (term936 A _43241 _43242) = (term936 A _43241 _43242).
Proof. exact (eq_refl (term936 A _43241 _43242)). Qed.
Lemma lem3768503 {A : Type'} (_43242 : A) (_43243 : A) (f : type686 A) (_43241 : A -> Prop) : (term1073 A _43242 f _43241 _43243) = (term1074 A _43242 _43243 f _43241).
Proof. exact (MK_COMB (@lem3768502 A _43241 _43242) (@lem3768496 A _43243 f _43241)). Qed.
Lemma lem3768514 {A : Type'} (_43242 : A) (_43243 : A) (f : type686 A) (_43241 : A -> Prop) : (term1072 A f _43242 _43241 _43243) = (term1074 A _43242 _43243 f _43241).
Proof. exact (TRANS (@lem3768481 A _43242 f _43241 _43243) (@lem3768503 A _43242 _43243 f _43241)). Qed.
Lemma lem3768515 {A : Type'} (s : A -> Prop) (_43242 : A) : (term949 A s _43242) = (term949 A s _43242).
Proof. exact (eq_refl (term949 A s _43242)). Qed.
Lemma lem3768516 {A : Type'} (s : A -> Prop) (_43242 : A) (_43243 : A) (f : type686 A) (_43241 : A -> Prop) : (term1070 A s f _43242 _43241 _43243) = (term1075 A s _43242 _43243 f _43241).
Proof. exact (MK_COMB (@lem3768515 A s _43242) (@lem3768514 A _43242 _43243 f _43241)). Qed.
Lemma lem3768520 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3768521 {A : Type'} (s : A -> Prop) (_43242 : A) (_43243 : A) (f : type686 A) (_43241 : A -> Prop) : (term1075 A s _43242 _43243 f _43241) = (term1076 A s _43242 _43243 f _43241).
Proof. exact (@lem3768520 (@I (A -> Prop) _43241 _43242) (term926 A s _43242) (term1038 A _43243 f _43241)). Qed.
Lemma lem3768535 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3768536 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : (term1063 A s _43242 _43243 f _43241) = (term1064 A _43243 s _43242 f _43241).
Proof. exact (@lem3768535 (term926 A _43241 _43243) (term926 A s _43242) (term927 A f _43241)). Qed.
Lemma lem3768552 {A : Type'} (_43241 : A -> Prop) (_43242 : A) : (term936 A _43241 _43242) = (term936 A _43241 _43242).
Proof. exact (eq_refl (term936 A _43241 _43242)). Qed.
Lemma lem3768553 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : (term1076 A s _43242 _43243 f _43241) = (term1077 A _43243 s _43242 f _43241).
Proof. exact (MK_COMB (@lem3768552 A _43241 _43242) (@lem3768536 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768564 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : (term1075 A s _43242 _43243 f _43241) = (term1077 A _43243 s _43242 f _43241).
Proof. exact (TRANS (@lem3768521 A s _43242 _43243 f _43241) (@lem3768553 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768565 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : (term1070 A s f _43242 _43241 _43243) = (term1077 A _43243 s _43242 f _43241).
Proof. exact (TRANS (@lem3768516 A s _43242 _43243 f _43241) (@lem3768564 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768566 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : (term1069 A f s _43242 _43241 _43243) = (term1077 A _43243 s _43242 f _43241).
Proof. exact (TRANS (@lem3768466 A s f _43242 _43241 _43243) (@lem3768565 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768567 {A : Type'} (s : A -> Prop) (_43243 : A) : (term936 A s _43243) = (term936 A s _43243).
Proof. exact (eq_refl (term936 A s _43243)). Qed.
Lemma lem3768568 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : (term1078 A f s _43242 _43241 _43243) = (term1079 A _43243 s _43242 f _43241).
Proof. exact (MK_COMB (@lem3768567 A s _43243) (@lem3768566 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768572 (q : Prop) (p : Prop) (r : Prop) : (term51 p q r) = (term51 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3768573 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : (term1079 A _43243 s _43242 f _43241) = (term1066 A _43243 s _43242 f _43241).
Proof. exact (@lem3768572 (@I (A -> Prop) _43241 _43242) (@I (A -> Prop) s _43243) (term1064 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768609 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : (term1078 A f s _43242 _43241 _43243) = (term1066 A _43243 s _43242 f _43241).
Proof. exact (TRANS (@lem3768568 A _43243 s _43242 f _43241) (@lem3768573 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768610 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : ((term1034 A f _43242 _43241 s _43243) = (term1078 A f s _43242 _43241 _43243)) = ((term1066 A _43243 s _43242 f _43241) = (term1066 A _43243 s _43242 f _43241)).
Proof. exact (MK_COMB (@lem3768451 A _43243 s _43242 f _43241) (@lem3768609 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768612 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3768613 (x : Prop) : (x = x) = True.
Proof. exact (@lem3768612 Prop x). Qed.
Lemma lem3768614 {A : Type'} (_43243 : A) (s : A -> Prop) (_43242 : A) (f : type686 A) (_43241 : A -> Prop) : ((term1066 A _43243 s _43242 f _43241) = (term1066 A _43243 s _43242 f _43241)) = True.
Proof. exact (@lem3768613 (term1066 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768615 {A : Type'} (f : type686 A) (s : A -> Prop) (_43242 : A) (_43241 : A -> Prop) (_43243 : A) : ((term1034 A f _43242 _43241 s _43243) = (term1078 A f s _43242 _43241 _43243)) = True.
Proof. exact (TRANS (@lem3768610 A _43243 s _43242 f _43241) (@lem3768614 A _43243 s _43242 f _43241)). Qed.
Lemma lem3768616 {A : Type'} (f : type686 A) (s : A -> Prop) (_43242 : A) (_43241 : A -> Prop) (_43243 : A) : True = ((term1034 A f _43242 _43241 s _43243) = (term1078 A f s _43242 _43241 _43243)).
Proof. exact (SYM (@lem3768615 A f s _43242 _43241 _43243)). Qed.
Lemma lem3768617 {A : Type'} (f : type686 A) (s : A -> Prop) (_43242 : A) (_43241 : A -> Prop) (_43243 : A) : (term1034 A f _43242 _43241 s _43243) = (term1078 A f s _43242 _43241 _43243).
Proof. exact (EQ_MP (@lem3768616 A f s _43242 _43241 _43243) (@lem0)). Qed.
Lemma lem3768618 {A : Type'} (_43242 : A) (_43241 : A -> Prop) (_43243 : A) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term1078 A f s _43242 _43241 _43243.
Proof. exact (EQ_MP (@lem3768617 A f s _43242 _43241 _43243) (@lem3767569 A _43242 _43241 _43243 s f x'' h1)). Qed.
Lemma lem3768620 (b : Prop) (a : Prop) : (a \/ b) = (term55 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3768621 {A : Type'} (f : type686 A) (_43242 : A) (_43241 : A -> Prop) (s : A -> Prop) (_43243 : A) : (term1078 A f s _43242 _43241 _43243) = (term1080 A f _43242 _43241 s _43243).
Proof. exact (@lem3768620 (term1069 A f s _43242 _43241 _43243) (@I (A -> Prop) s _43243)). Qed.
Lemma lem3768623 (a : Prop) (b : Prop) : (term58 a b) = (term59 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3768624 {A : Type'} (f : type686 A) (s : A -> Prop) (_43242 : A) (_43241 : A -> Prop) (_43243 : A) : (term1081 A f s _43242 _43241 _43243) = (term1082 A f s _43242 _43241 _43243).
Proof. exact (@lem3768623 (term927 A f _43241) (term1083 A s _43242 _43241 _43243)). Qed.
Lemma lem3768626 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3768627 {A : Type'} (f : type686 A) (_43241 : A -> Prop) : (term1042 A f _43241) = (@I ((A -> Prop) -> Prop) f _43241).
Proof. exact (@lem3768626 (@I ((A -> Prop) -> Prop) f _43241)). Qed.
Lemma lem3768628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3768629 {A : Type'} (f : type686 A) (_43241 : A -> Prop) : (term1084 A f _43241) = (term924 A f _43241).
Proof. exact (MK_COMB (@lem3768628) (@lem3768627 A f _43241)). Qed.
Lemma lem3768631 (a : Prop) (b : Prop) : (term58 a b) = (term59 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3768632 {A : Type'} (s : A -> Prop) (_43242 : A) (_43241 : A -> Prop) (_43243 : A) : (term1085 A s _43242 _43241 _43243) = (term1086 A s _43242 _43241 _43243).
Proof. exact (@lem3768631 (term926 A s _43242) (term1071 A _43242 _43241 _43243)). Qed.
Lemma lem3768634 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3768635 {A : Type'} (s : A -> Prop) (_43242 : A) : (term1087 A s _43242) = (@I (A -> Prop) s _43242).
Proof. exact (@lem3768634 (@I (A -> Prop) s _43242)). Qed.
Lemma lem3768636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3768637 {A : Type'} (s : A -> Prop) (_43242 : A) : (term1088 A s _43242) = (term1089 A s _43242).
Proof. exact (MK_COMB (@lem3768636) (@lem3768635 A s _43242)). Qed.
Lemma lem3768639 (a : Prop) (b : Prop) : (term58 a b) = (term59 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3768640 {A : Type'} (_43242 : A) (_43241 : A -> Prop) (_43243 : A) : (term1090 A _43242 _43241 _43243) = (term1091 A _43242 _43241 _43243).
Proof. exact (@lem3768639 (@I (A -> Prop) _43241 _43242) (term926 A _43241 _43243)). Qed.
Lemma lem3768642 (a : Prop) : (term8 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3768643 {A : Type'} (_43241 : A -> Prop) (_43243 : A) : (term1087 A _43241 _43243) = (@I (A -> Prop) _43241 _43243).
Proof. exact (@lem3768642 (@I (A -> Prop) _43241 _43243)). Qed.
Lemma lem3768644 {A : Type'} (_43241 : A -> Prop) (_43242 : A) : (term932 A _43241 _43242) = (term932 A _43241 _43242).
Proof. exact (eq_refl (term932 A _43241 _43242)). Qed.
Lemma lem3768645 {A : Type'} (_43242 : A) (_43241 : A -> Prop) (_43243 : A) : (term1091 A _43242 _43241 _43243) = (term1092 A _43242 _43241 _43243).
Proof. exact (MK_COMB (@lem3768644 A _43241 _43242) (@lem3768643 A _43241 _43243)). Qed.
Lemma lem3768646 {A : Type'} (_43242 : A) (_43241 : A -> Prop) (_43243 : A) : (term1090 A _43242 _43241 _43243) = (term1092 A _43242 _43241 _43243).
Proof. exact (TRANS (@lem3768640 A _43242 _43241 _43243) (@lem3768645 A _43242 _43241 _43243)). Qed.
Lemma lem3768647 {A : Type'} (s : A -> Prop) (_43242 : A) (_43241 : A -> Prop) (_43243 : A) : (term1086 A s _43242 _43241 _43243) = (term1093 A s _43242 _43241 _43243).
Proof. exact (MK_COMB (@lem3768637 A s _43242) (@lem3768646 A _43242 _43241 _43243)). Qed.
Lemma lem3768648 {A : Type'} (s : A -> Prop) (_43242 : A) (_43241 : A -> Prop) (_43243 : A) : (term1085 A s _43242 _43241 _43243) = (term1093 A s _43242 _43241 _43243).
Proof. exact (TRANS (@lem3768632 A s _43242 _43241 _43243) (@lem3768647 A s _43242 _43241 _43243)). Qed.
Lemma lem3768649 {A : Type'} (f : type686 A) (s : A -> Prop) (_43242 : A) (_43241 : A -> Prop) (_43243 : A) : (term1082 A f s _43242 _43241 _43243) = (term1094 A f s _43242 _43241 _43243).
Proof. exact (MK_COMB (@lem3768629 A f _43241) (@lem3768648 A s _43242 _43241 _43243)). Qed.
Lemma lem3768650 {A : Type'} (f : type686 A) (s : A -> Prop) (_43242 : A) (_43241 : A -> Prop) (_43243 : A) : (term1081 A f s _43242 _43241 _43243) = (term1094 A f s _43242 _43241 _43243).
Proof. exact (TRANS (@lem3768624 A f s _43242 _43241 _43243) (@lem3768649 A f s _43242 _43241 _43243)). Qed.
Lemma lem3768651 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3768652 {A : Type'} (f : type686 A) (s : A -> Prop) (_43242 : A) (_43241 : A -> Prop) (_43243 : A) : (term1095 A f s _43242 _43241 _43243) = (term1096 A f s _43242 _43241 _43243).
Proof. exact (MK_COMB (@lem3768651) (@lem3768650 A f s _43242 _43241 _43243)). Qed.
Lemma lem3768653 {A : Type'} (s : A -> Prop) (_43243 : A) : (@I (A -> Prop) s _43243) = (@I (A -> Prop) s _43243).
Proof. exact (eq_refl (@I (A -> Prop) s _43243)). Qed.
Lemma lem3768654 {A : Type'} (f : type686 A) (_43242 : A) (_43241 : A -> Prop) (s : A -> Prop) (_43243 : A) : (term1080 A f _43242 _43241 s _43243) = (term1097 A f _43242 _43241 s _43243).
Proof. exact (MK_COMB (@lem3768652 A f s _43242 _43241 _43243) (@lem3768653 A s _43243)). Qed.
Lemma lem3768655 {A : Type'} (f : type686 A) (_43242 : A) (_43241 : A -> Prop) (s : A -> Prop) (_43243 : A) : (term1078 A f s _43242 _43241 _43243) = (term1097 A f _43242 _43241 s _43243).
Proof. exact (TRANS (@lem3768621 A f _43242 _43241 s _43243) (@lem3768654 A f _43242 _43241 s _43243)). Qed.
Lemma lem3768657 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term925 A f t x) (h2 : term939 A s t' f x') : term1092 A x' t x.
Proof. exact (conj (@lem3768268 A t x s t' f x' h1 h2) (@lem3768275 A f t x h1)). Qed.
Lemma lem3768658 {A : Type'} (t : A -> Prop) (x : A) (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (x' : A) (h1 : term925 A f t x) (h2 : term939 A s t' f x') (h3 : @I (A -> Prop) s x') : term1093 A s x' t x.
Proof. exact (conj (@lem3768208 A s x' h3) (@lem3768657 A t x s t' f x' h1 h2)). Qed.
Lemma lem3768659 {A : Type'} (t : A -> Prop) (x : A) (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (x' : A) (h1 : term925 A f t x) (h2 : term939 A s t' f x') (h3 : @I (A -> Prop) s x') : term1094 A f s x' t x.
Proof. exact (conj (@lem3768201 A f t x h1) (@lem3768658 A t x t' f s x' h1 h2 h3)). Qed.
Lemma lem3768661 {A : Type'} (_43242 : A) (_43241 : A -> Prop) (_43243 : A) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term1097 A f _43242 _43241 s _43243.
Proof. exact (EQ_MP (@lem3768655 A f _43242 _43241 s _43243) (@lem3768618 A _43242 _43241 _43243 s f x'' h1)). Qed.
Lemma lem3768662 {A : Type'} (_43242 : A) (_43241 : A -> Prop) (_43243 : A) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term1097 A f _43242 _43241 s _43243.
Proof. exact (@lem3768661 A _43242 _43241 _43243 s f x'' h1). Qed.
Lemma lem3768663 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (x'' : A -> Prop) (h1 : term620 A s f x'') : term1097 A f x' t s x.
Proof. exact (@lem3768662 A x' t x s f x'' h1). Qed.
Lemma lem3768666 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (x' : A) (h1 : term620 A s f x'') (h2 : term925 A f t x) (h3 : term939 A s t' f x') (h4 : @I (A -> Prop) s x') : @I (A -> Prop) s x.
Proof. exact (@lem3768663 A x' t x s f x'' h1 (@lem3768659 A t x t' f s x' h2 h3 h4)). Qed.
Lemma lem3768667 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (x' : A) (h1 : term620 A s f x'') (h2 : term925 A f t x) (h3 : term939 A s t' f x') (h4 : @I (A -> Prop) s x') : term1035 A s x.
Proof. exact (fun h0 : term926 A s x => @lem3768666 A x'' t x t' f s x' h1 h2 h3 h4). Qed.
Lemma lem3768669 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768670 {A : Type'} (s : A -> Prop) (x : A) : (term1035 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3768669 (@I (A -> Prop) s x)). Qed.
Lemma lem3768671 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (x' : A) (h1 : term620 A s f x'') (h2 : term925 A f t x) (h3 : term939 A s t' f x') (h4 : @I (A -> Prop) s x') : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3768670 A s x) (@lem3768667 A x'' t x t' f s x' h1 h2 h3 h4)). Qed.
Lemma lem3768674 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3768676 {A : Type'} (s : A -> Prop) (x : A) : (term926 A s x) = (term1036 A s x).
Proof. exact (@lem3768674 (@I (A -> Prop) s x)). Qed.
Lemma lem3768679 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) : term1036 A s x.
Proof. exact (EQ_MP (@lem3768676 A s x) (@lem3767581 A f t s x h1)). Qed.
Lemma lem3768682 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (x' : A) (h1 : term620 A s f x'') (h2 : term925 A f t x) (h3 : term943 A f t s x) (h4 : term939 A s t' f x') (h5 : @I (A -> Prop) s x') : False.
Proof. exact (@lem3768679 A f t s x h3 (@lem3768671 A x'' t x t' f s x' h1 h2 h4 h5)). Qed.
Lemma lem3768683 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (x' : A) (h1 : term620 A s f x'') (h2 : term925 A f t x) (h3 : term943 A f t s x) (h4 : term939 A s t' f x') (h5 : @I (A -> Prop) s x') : term32.
Proof. exact (fun h0 : ~ False => @lem3768682 A x'' t x t' f s x' h1 h2 h3 h4 h5). Qed.
Lemma lem3768685 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768686 : term32 = False.
Proof. exact (@lem3768685 False). Qed.
Lemma lem3768687 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (x' : A) (h1 : term620 A s f x'') (h2 : term925 A f t x) (h3 : term943 A f t s x) (h4 : term939 A s t' f x') (h5 : @I (A -> Prop) s x') : False.
Proof. exact (EQ_MP (@lem3768686) (@lem3768683 A x'' t x t' f s x' h1 h2 h3 h4 h5)). Qed.
Lemma lem3768689 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem3762366 A f s x h1)). Qed.
Lemma lem3768690 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term1035 A s x.
Proof. exact (fun h0 : term926 A s x => @lem3768689 A f s x h1). Qed.
Lemma lem3768692 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768693 {A : Type'} (s : A -> Prop) (x : A) : (term1035 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3768692 (@I (A -> Prop) s x)). Qed.
Lemma lem3768694 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3768693 A s x) (@lem3768690 A f s x h1)). Qed.
Lemma lem3768697 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3768699 {A : Type'} (s : A -> Prop) (x : A) : (term926 A s x) = (term1036 A s x).
Proof. exact (@lem3768697 (@I (A -> Prop) s x)). Qed.
Lemma lem3768702 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term1036 A s x.
Proof. exact (EQ_MP (@lem3768699 A s x) (@lem3767663 A f s x h1)). Qed.
Lemma lem3768705 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : False.
Proof. exact (@lem3768702 A f s x h1 (@lem3768694 A f s x h1)). Qed.
Lemma lem3768706 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term32.
Proof. exact (fun h0 : ~ False => @lem3768705 A f s x h1). Qed.
Lemma lem3768708 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768709 : term32 = False.
Proof. exact (@lem3768708 False). Qed.
Lemma lem3768710 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : False.
Proof. exact (EQ_MP (@lem3768709) (@lem3768706 A f s x h1)). Qed.
Lemma lem3768712 {A : Type'} (s : A -> Prop) (x : A) (h1 : @I (A -> Prop) s x) : @I (A -> Prop) s x.
Proof. exact (h1). Qed.
Lemma lem3768713 {A : Type'} (s : A -> Prop) (x : A) (h1 : @I (A -> Prop) s x) : term1035 A s x.
Proof. exact (fun h0 : term926 A s x => @lem3768712 A s x h1). Qed.
Lemma lem3768715 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768716 {A : Type'} (s : A -> Prop) (x : A) : (term1035 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3768715 (@I (A -> Prop) s x)). Qed.
Lemma lem3768717 {A : Type'} (s : A -> Prop) (x : A) (h1 : @I (A -> Prop) s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3768716 A s x) (@lem3768713 A s x h1)). Qed.
Lemma lem3768720 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3768722 {A : Type'} (s : A -> Prop) (x : A) : (term926 A s x) = (term1036 A s x).
Proof. exact (@lem3768720 (@I (A -> Prop) s x)). Qed.
Lemma lem3768725 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) : term1036 A s x.
Proof. exact (EQ_MP (@lem3768722 A s x) (@lem3767747 A f t s x h1)). Qed.
Lemma lem3768728 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : False.
Proof. exact (@lem3768725 A f t s x h1 (@lem3768717 A s x h2)). Qed.
Lemma lem3768729 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : term32.
Proof. exact (fun h0 : ~ False => @lem3768728 A f t s x h1 h2). Qed.
Lemma lem3768731 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768732 : term32 = False.
Proof. exact (@lem3768731 False). Qed.
Lemma lem3768733 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3768732) (@lem3768729 A f t s x h1 h2)). Qed.
Lemma lem3768735 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term925 A f t' x') : @I ((A -> Prop) -> Prop) f t'.
Proof. exact (proj1 (@lem3762364 A f t' x' h1)). Qed.
Lemma lem3768736 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term925 A f t' x') : term1037 A f t'.
Proof. exact (fun h0 : term927 A f t' => @lem3768735 A f t' x' h1). Qed.
Lemma lem3768738 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768739 {A : Type'} (f : type686 A) (t' : A -> Prop) : (term1037 A f t') = (@I ((A -> Prop) -> Prop) f t').
Proof. exact (@lem3768738 (@I ((A -> Prop) -> Prop) f t')). Qed.
Lemma lem3768740 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term925 A f t' x') : @I ((A -> Prop) -> Prop) f t'.
Proof. exact (EQ_MP (@lem3768739 A f t') (@lem3768736 A f t' x' h1)). Qed.
Lemma lem3768742 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term925 A f t' x') : @I (A -> Prop) t' x'.
Proof. exact (proj2 (@lem3762364 A f t' x' h1)). Qed.
Lemma lem3768743 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term925 A f t' x') : term1035 A t' x'.
Proof. exact (fun h0 : term926 A t' x' => @lem3768742 A f t' x' h1). Qed.
Lemma lem3768745 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768746 {A : Type'} (t' : A -> Prop) (x' : A) : (term1035 A t' x') = (@I (A -> Prop) t' x').
Proof. exact (@lem3768745 (@I (A -> Prop) t' x')). Qed.
Lemma lem3768747 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term925 A f t' x') : @I (A -> Prop) t' x'.
Proof. exact (EQ_MP (@lem3768746 A t' x') (@lem3768743 A f t' x' h1)). Qed.
Lemma lem3768749 (a : Prop) (b : Prop) : (term1098 a b) = (term1099 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3768750 {A : Type'} (f : type686 A) (_43278 : A -> Prop) (x' : A) : (term929 A f _43278 x') = (term1100 A f _43278 x').
Proof. exact (@lem3768749 (@I ((A -> Prop) -> Prop) f _43278) (@I (A -> Prop) _43278 x')). Qed.
Lemma lem3768752 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3768753 {A : Type'} (f : type686 A) (_43278 : A -> Prop) (x' : A) : (term1100 A f _43278 x') = (term1101 A f _43278 x').
Proof. exact (@lem3768752 (term925 A f _43278 x')). Qed.
Lemma lem3768754 {A : Type'} (f : type686 A) (_43278 : A -> Prop) (x' : A) : (term929 A f _43278 x') = (term1101 A f _43278 x').
Proof. exact (TRANS (@lem3768750 A f _43278 x') (@lem3768753 A f _43278 x')). Qed.
Lemma lem3768756 {A : Type'} (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term925 A f t' x') : term925 A f t' x'.
Proof. exact (conj (@lem3768740 A f t' x' h1) (@lem3768747 A f t' x' h1)). Qed.
Lemma lem3768758 {A : Type'} (_43278 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term939 A s t' f x') : term1101 A f _43278 x'.
Proof. exact (EQ_MP (@lem3768754 A f _43278 x') (@lem3767821 A _43278 s t' f x' h1)). Qed.
Lemma lem3768759 {A : Type'} (_43278 : A -> Prop) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term939 A s t' f x') : term1101 A f _43278 x'.
Proof. exact (@lem3768758 A _43278 s t' f x' h1). Qed.
Lemma lem3768760 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term939 A s t' f x') : term1101 A f t' x'.
Proof. exact (@lem3768759 A t' s t' f x' h1). Qed.
Lemma lem3768763 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term925 A f t' x') (h2 : term939 A s t' f x') : False.
Proof. exact (@lem3768760 A s t' f x' h2 (@lem3768756 A f t' x' h1)). Qed.
Lemma lem3768764 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term925 A f t' x') (h2 : term939 A s t' f x') : term32.
Proof. exact (fun h0 : ~ False => @lem3768763 A s t' f x' h1 h2). Qed.
Lemma lem3768766 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768767 : term32 = False.
Proof. exact (@lem3768766 False). Qed.
Lemma lem3768768 {A : Type'} (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term925 A f t' x') (h2 : term939 A s t' f x') : False.
Proof. exact (EQ_MP (@lem3768767) (@lem3768764 A s t' f x' h1 h2)). Qed.
Lemma lem3768770 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem3762380 A f s x h1)). Qed.
Lemma lem3768771 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term1035 A s x.
Proof. exact (fun h0 : term926 A s x => @lem3768770 A f s x h1). Qed.
Lemma lem3768773 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768774 {A : Type'} (s : A -> Prop) (x : A) : (term1035 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3768773 (@I (A -> Prop) s x)). Qed.
Lemma lem3768775 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3768774 A s x) (@lem3768771 A f s x h1)). Qed.
Lemma lem3768778 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3768780 {A : Type'} (s : A -> Prop) (x : A) : (term926 A s x) = (term1036 A s x).
Proof. exact (@lem3768778 (@I (A -> Prop) s x)). Qed.
Lemma lem3768783 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term1036 A s x.
Proof. exact (EQ_MP (@lem3768780 A s x) (@lem3767911 A f s x h1)). Qed.
Lemma lem3768786 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : False.
Proof. exact (@lem3768783 A f s x h1 (@lem3768775 A f s x h1)). Qed.
Lemma lem3768787 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term32.
Proof. exact (fun h0 : ~ False => @lem3768786 A f s x h1). Qed.
Lemma lem3768789 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768790 : term32 = False.
Proof. exact (@lem3768789 False). Qed.
Lemma lem3768791 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : False.
Proof. exact (EQ_MP (@lem3768790) (@lem3768787 A f s x h1)). Qed.
Lemma lem3768793 {A : Type'} (s : A -> Prop) (x : A) (h1 : @I (A -> Prop) s x) : @I (A -> Prop) s x.
Proof. exact (h1). Qed.
Lemma lem3768794 {A : Type'} (s : A -> Prop) (x : A) (h1 : @I (A -> Prop) s x) : term1035 A s x.
Proof. exact (fun h0 : term926 A s x => @lem3768793 A s x h1). Qed.
Lemma lem3768796 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768797 {A : Type'} (s : A -> Prop) (x : A) : (term1035 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3768796 (@I (A -> Prop) s x)). Qed.
Lemma lem3768798 {A : Type'} (s : A -> Prop) (x : A) (h1 : @I (A -> Prop) s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3768797 A s x) (@lem3768794 A s x h1)). Qed.
Lemma lem3768801 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3768803 {A : Type'} (s : A -> Prop) (x : A) : (term926 A s x) = (term1036 A s x).
Proof. exact (@lem3768801 (@I (A -> Prop) s x)). Qed.
Lemma lem3768806 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) : term1036 A s x.
Proof. exact (EQ_MP (@lem3768803 A s x) (@lem3767997 A f t s x h1)). Qed.
Lemma lem3768809 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : False.
Proof. exact (@lem3768806 A f t s x h1 (@lem3768798 A s x h2)). Qed.
Lemma lem3768810 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : term32.
Proof. exact (fun h0 : ~ False => @lem3768809 A f t s x h1 h2). Qed.
Lemma lem3768812 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768813 : term32 = False.
Proof. exact (@lem3768812 False). Qed.
Lemma lem3768814 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3768813) (@lem3768810 A f t s x h1 h2)). Qed.
Lemma lem3768816 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : @I ((A -> Prop) -> Prop) f t'.
Proof. exact (proj1 (@lem3762391 A s f t' x' h1)). Qed.
Lemma lem3768817 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term1037 A f t'.
Proof. exact (fun h0 : term927 A f t' => @lem3768816 A s f t' x' h1). Qed.
Lemma lem3768819 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768820 {A : Type'} (f : type686 A) (t' : A -> Prop) : (term1037 A f t') = (@I ((A -> Prop) -> Prop) f t').
Proof. exact (@lem3768819 (@I ((A -> Prop) -> Prop) f t')). Qed.
Lemma lem3768821 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : @I ((A -> Prop) -> Prop) f t'.
Proof. exact (EQ_MP (@lem3768820 A f t') (@lem3768817 A s f t' x' h1)). Qed.
Lemma lem3768823 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : @I (A -> Prop) t' x'.
Proof. exact (proj2 (@lem3762391 A s f t' x' h1)). Qed.
Lemma lem3768824 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term1035 A t' x'.
Proof. exact (fun h0 : term926 A t' x' => @lem3768823 A s f t' x' h1). Qed.
Lemma lem3768826 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768827 {A : Type'} (t' : A -> Prop) (x' : A) : (term1035 A t' x') = (@I (A -> Prop) t' x').
Proof. exact (@lem3768826 (@I (A -> Prop) t' x')). Qed.
Lemma lem3768828 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : @I (A -> Prop) t' x'.
Proof. exact (EQ_MP (@lem3768827 A t' x') (@lem3768824 A s f t' x' h1)). Qed.
Lemma lem3768830 (a : Prop) (b : Prop) : (term1098 a b) = (term1099 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3768831 {A : Type'} (f : type686 A) (_43312 : A -> Prop) (x' : A) : (term929 A f _43312 x') = (term1100 A f _43312 x').
Proof. exact (@lem3768830 (@I ((A -> Prop) -> Prop) f _43312) (@I (A -> Prop) _43312 x')). Qed.
Lemma lem3768833 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3768834 {A : Type'} (f : type686 A) (_43312 : A -> Prop) (x' : A) : (term1100 A f _43312 x') = (term1101 A f _43312 x').
Proof. exact (@lem3768833 (term925 A f _43312 x')). Qed.
Lemma lem3768835 {A : Type'} (f : type686 A) (_43312 : A -> Prop) (x' : A) : (term929 A f _43312 x') = (term1101 A f _43312 x').
Proof. exact (TRANS (@lem3768831 A f _43312 x') (@lem3768834 A f _43312 x')). Qed.
Lemma lem3768837 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term925 A f t' x'.
Proof. exact (conj (@lem3768821 A s f t' x' h1) (@lem3768828 A s f t' x' h1)). Qed.
Lemma lem3768839 {A : Type'} (_43312 : A -> Prop) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term1101 A f _43312 x'.
Proof. exact (EQ_MP (@lem3768835 A f _43312 x') (@lem3768077 A _43312 s f t' x' h1)). Qed.
Lemma lem3768840 {A : Type'} (_43312 : A -> Prop) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term1101 A f _43312 x'.
Proof. exact (@lem3768839 A _43312 s f t' x' h1). Qed.
Lemma lem3768841 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term1101 A f t' x'.
Proof. exact (@lem3768840 A t' s f t' x' h1). Qed.
Lemma lem3768844 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : False.
Proof. exact (@lem3768841 A s f t' x' h1 (@lem3768837 A s f t' x' h1)). Qed.
Lemma lem3768845 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : term32.
Proof. exact (fun h0 : ~ False => @lem3768844 A s f t' x' h1). Qed.
Lemma lem3768847 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768848 : term32 = False.
Proof. exact (@lem3768847 False). Qed.
Lemma lem3768849 {A : Type'} (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') : False.
Proof. exact (EQ_MP (@lem3768848) (@lem3768845 A s f t' x' h1)). Qed.
Lemma lem3768851 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem3762398 A f s x h1)). Qed.
Lemma lem3768852 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term1035 A s x.
Proof. exact (fun h0 : term926 A s x => @lem3768851 A f s x h1). Qed.
Lemma lem3768854 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768855 {A : Type'} (s : A -> Prop) (x : A) : (term1035 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3768854 (@I (A -> Prop) s x)). Qed.
Lemma lem3768856 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3768855 A s x) (@lem3768852 A f s x h1)). Qed.
Lemma lem3768859 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3768861 {A : Type'} (s : A -> Prop) (x : A) : (term926 A s x) = (term1036 A s x).
Proof. exact (@lem3768859 (@I (A -> Prop) s x)). Qed.
Lemma lem3768864 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term1036 A s x.
Proof. exact (EQ_MP (@lem3768861 A s x) (@lem3768165 A f s x h1)). Qed.
Lemma lem3768867 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : False.
Proof. exact (@lem3768864 A f s x h1 (@lem3768856 A f s x h1)). Qed.
Lemma lem3768868 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : term32.
Proof. exact (fun h0 : ~ False => @lem3768867 A f s x h1). Qed.
Lemma lem3768870 (p : Prop) : (term30 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3768871 : term32 = False.
Proof. exact (@lem3768870 False). Qed.
Lemma lem3768872 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term942 A f s x) : False.
Proof. exact (EQ_MP (@lem3768871) (@lem3768868 A f s x h1)). Qed.
Lemma lem3768873 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : (@I (A -> Prop) s x) = False.
Proof. exact (prop_ext (fun h3 : @I (A -> Prop) s x => @lem3768814 A f t s x h1 h2) (fun h3 : False => @lem3767999 A s x h2)). Qed.
Lemma lem3768874 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3768873 A f t s x h1 h2) (@lem3767999 A s x h2)). Qed.
Lemma lem3768875 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : (@I (A -> Prop) s x) = False.
Proof. exact (prop_ext (fun h3 : @I (A -> Prop) s x => @lem3768733 A f t s x h1 h2) (fun h3 : False => @lem3767749 A s x h2)). Qed.
Lemma lem3768876 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3768875 A f t s x h1 h2) (@lem3767749 A s x h2)). Qed.
Lemma lem3768877 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (x' : A) (h1 : term620 A s f x'') (h2 : term925 A f t x) (h3 : term943 A f t s x) (h4 : term939 A s t' f x') (h5 : @I (A -> Prop) s x') : (@I (A -> Prop) s x') = False.
Proof. exact (prop_ext (fun h6 : @I (A -> Prop) s x' => @lem3768687 A x'' t x t' f s x' h1 h2 h3 h4 h5) (fun h6 : False => @lem3767579 A s x' h5)). Qed.
Lemma lem3768878 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (x' : A) (h1 : term620 A s f x'') (h2 : term925 A f t x) (h3 : term943 A f t s x) (h4 : term939 A s t' f x') (h5 : @I (A -> Prop) s x') : False.
Proof. exact (EQ_MP (@lem3768877 A x'' t x t' f s x' h1 h2 h3 h4 h5) (@lem3767579 A s x' h5)). Qed.
Lemma lem3768879 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : (@I (A -> Prop) s x) = False.
Proof. exact (prop_ext (fun h3 : @I (A -> Prop) s x => @lem3768194 A f t s x h1 h2) (fun h3 : False => @lem3767505 A s x h2)). Qed.
Lemma lem3768880 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3768879 A f t s x h1 h2) (@lem3767505 A s x h2)). Qed.
Lemma lem3768881 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : (@I (A -> Prop) s x) = False.
Proof. exact (prop_ext (fun h3 : @I (A -> Prop) s x => @lem3768874 A f t s x h1 h2) (fun h3 : False => @lem3766060 A s x h2)). Qed.
Lemma lem3768882 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3768881 A f t s x h1 h2) (@lem3766060 A s x h2)). Qed.
Lemma lem3768883 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : (@I (A -> Prop) s x) = False.
Proof. exact (prop_ext (fun h3 : @I (A -> Prop) s x => @lem3768876 A f t s x h1 h2) (fun h3 : False => @lem3764485 A s x h2)). Qed.
Lemma lem3768884 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3768883 A f t s x h1 h2) (@lem3764485 A s x h2)). Qed.
Lemma lem3768885 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (x' : A) (h1 : term620 A s f x'') (h2 : term925 A f t x) (h3 : term943 A f t s x) (h4 : term939 A s t' f x') (h5 : @I (A -> Prop) s x') : (@I (A -> Prop) s x') = False.
Proof. exact (prop_ext (fun h6 : @I (A -> Prop) s x' => @lem3768878 A x'' t x t' f s x' h1 h2 h3 h4 h5) (fun h6 : False => @lem3763428 A s x' h5)). Qed.
Lemma lem3768886 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (x' : A) (h1 : term620 A s f x'') (h2 : term925 A f t x) (h3 : term943 A f t s x) (h4 : term939 A s t' f x') (h5 : @I (A -> Prop) s x') : False.
Proof. exact (EQ_MP (@lem3768885 A x'' t x t' f s x' h1 h2 h3 h4 h5) (@lem3763428 A s x' h5)). Qed.
Lemma lem3768887 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : (@I (A -> Prop) s x) = False.
Proof. exact (prop_ext (fun h3 : @I (A -> Prop) s x => @lem3768880 A f t s x h1 h2) (fun h3 : False => @lem3762922 A s x h2)). Qed.
Lemma lem3768888 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3768887 A f t s x h1 h2) (@lem3762922 A s x h2)). Qed.
Lemma lem3768889 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : (@I (A -> Prop) s x) = False.
Proof. exact (prop_ext (fun h3 : @I (A -> Prop) s x => @lem3768882 A f t s x h1 h2) (fun h3 : False => @lem3766060 A s x h2)). Qed.
Lemma lem3768890 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3768889 A f t s x h1 h2) (@lem3766060 A s x h2)). Qed.
Lemma lem3768891 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : (@I (A -> Prop) s x) = False.
Proof. exact (prop_ext (fun h3 : @I (A -> Prop) s x => @lem3768884 A f t s x h1 h2) (fun h3 : False => @lem3764485 A s x h2)). Qed.
Lemma lem3768892 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3768891 A f t s x h1 h2) (@lem3764485 A s x h2)). Qed.
Lemma lem3768893 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (x' : A) (h1 : term620 A s f x'') (h2 : term925 A f t x) (h3 : term943 A f t s x) (h4 : term939 A s t' f x') (h5 : @I (A -> Prop) s x') : (@I (A -> Prop) s x') = False.
Proof. exact (prop_ext (fun h6 : @I (A -> Prop) s x' => @lem3768886 A x'' t x t' f s x' h1 h2 h3 h4 h5) (fun h6 : False => @lem3763428 A s x' h5)). Qed.
Lemma lem3768894 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (x' : A) (h1 : term620 A s f x'') (h2 : term925 A f t x) (h3 : term943 A f t s x) (h4 : term939 A s t' f x') (h5 : @I (A -> Prop) s x') : False.
Proof. exact (EQ_MP (@lem3768893 A x'' t x t' f s x' h1 h2 h3 h4 h5) (@lem3763428 A s x' h5)). Qed.
Lemma lem3768895 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : (@I (A -> Prop) s x) = False.
Proof. exact (prop_ext (fun h3 : @I (A -> Prop) s x => @lem3768888 A f t s x h1 h2) (fun h3 : False => @lem3762922 A s x h2)). Qed.
Lemma lem3768896 {A : Type'} (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term943 A f t s x) (h2 : @I (A -> Prop) s x) : False.
Proof. exact (EQ_MP (@lem3768895 A f t s x h1 h2) (@lem3762922 A s x h2)). Qed.
Lemma lem3768897 {A : Type'} (t' : A -> Prop) (x' : A) (f : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term935 A s f t' x') (h2 : term943 A f t s x) : False.
Proof. exact (or_elim (@lem3762400 A f t s x h2) (fun h0 : @I (A -> Prop) s x => @lem3768890 A f t s x h2 h0) (fun h0 : term925 A f t x => @lem3768849 A s f t' x' h1)). Qed.
Lemma lem3768898 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term935 A s f t' x') (h2 : term914 A t x s f t' x') : False.
Proof. exact (or_elim (@lem3762358 A t x s f t' x' h2) (fun h0 : term943 A f t s x => @lem3768897 A t' x' f t s x h1 h0) (fun h0 : term942 A f s x => @lem3768872 A f s x h0)). Qed.
Lemma lem3768899 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term925 A f t' x') (h2 : term943 A f t s x) (h3 : term939 A s t' f x') : False.
Proof. exact (or_elim (@lem3762382 A f t s x h2) (fun h0 : @I (A -> Prop) s x => @lem3768892 A f t s x h2 h0) (fun h0 : term925 A f t x => @lem3768768 A s t' f x' h1 h3)). Qed.
Lemma lem3768900 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term925 A f t' x') (h2 : term914 A t x s f t' x') (h3 : term939 A s t' f x') : False.
Proof. exact (or_elim (@lem3762358 A t x s f t' x' h2) (fun h0 : term943 A f t s x => @lem3768899 A t x s t' f x' h1 h0 h3) (fun h0 : term942 A f s x => @lem3768791 A f s x h0)). Qed.
Lemma lem3768901 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (x' : A) (h1 : term620 A s f x'') (h2 : term943 A f t s x) (h3 : term939 A s t' f x') (h4 : @I (A -> Prop) s x') : False.
Proof. exact (or_elim (@lem3762368 A f t s x h2) (fun h0 : @I (A -> Prop) s x => @lem3768896 A f t s x h2 h0) (fun h0 : term925 A f t x => @lem3768894 A x'' t x t' f s x' h1 h0 h2 h3 h4)). Qed.
Lemma lem3768902 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (t' : A -> Prop) (f : type686 A) (s : A -> Prop) (x' : A) (h1 : term620 A s f x'') (h2 : term914 A t x s f t' x') (h3 : term939 A s t' f x') (h4 : @I (A -> Prop) s x') : False.
Proof. exact (or_elim (@lem3762358 A t x s f t' x' h2) (fun h0 : term943 A f t s x => @lem3768901 A x'' t x t' f s x' h1 h0 h3 h4) (fun h0 : term942 A f s x => @lem3768710 A f s x h0)). Qed.
Lemma lem3768903 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (t' : A -> Prop) (f : type686 A) (x' : A) (h1 : term620 A s f x'') (h2 : term914 A t x s f t' x') (h3 : term939 A s t' f x') : False.
Proof. exact (or_elim (@lem3762362 A s t' f x' h3) (fun h0 : @I (A -> Prop) s x' => @lem3768902 A x'' t x t' f s x' h1 h2 h3 h0) (fun h0 : term925 A f t' x' => @lem3768900 A t x s t' f x' h0 h2 h3)). Qed.
Lemma lem3768904 {A : Type'} (x'' : A -> Prop) (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term620 A s f x'') (h2 : term914 A t x s f t' x') : False.
Proof. exact (or_elim (@lem3762357 A t x s f t' x' h2) (fun h0 : term939 A s t' f x' => @lem3768903 A x'' t x s t' f x' h1 h2 h0) (fun h0 : term935 A s f t' x' => @lem3768898 A t x s f t' x' h0 h2)). Qed.
Lemma lem3768905 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (t' : A -> Prop) (x' : A) (h1 : term513 A s f) (h2 : term914 A t x s f t' x') : False.
Proof. exact (ex_elim (@lem3760926 A s f h1) (fun x'' : A -> Prop => fun h0 : term622 A s f x'' => @lem3768904 A x'' t x s f t' x' h0 h2)). Qed.
Lemma lem3768906 {A : Type'} (t : A -> Prop) (x : A) (x' : A) (s : A -> Prop) (f : type686 A) (h1 : term917 A t x s f x') (h2 : term513 A s f) : False.
Proof. exact (ex_elim (@lem3761890 A t x s f x' h1) (fun t' : A -> Prop => fun h0 : term916 A t x s f x' t' => @lem3768905 A t x s f t' x' h2 h0)). Qed.
Lemma lem3768907 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (f : type686 A) (h1 : term919 A t x s f) (h2 : term513 A s f) : False.
Proof. exact (ex_elim (@lem3761889 A t x s f h1) (fun x' : A => fun h0 : term918 A t x s f x' => @lem3768906 A t x x' s f h0 h2)). Qed.
Lemma lem3768908 {A : Type'} (x : A) (s : A -> Prop) (f : type686 A) (h1 : term921 A x s f) (h2 : term513 A s f) : False.
Proof. exact (ex_elim (@lem3761888 A x s f h1) (fun t : A -> Prop => fun h0 : term920 A x s f t => @lem3768907 A t x s f h0 h2)). Qed.
Lemma lem3768909 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term557 A s f) (h2 : term513 A s f) : False.
Proof. exact (ex_elim (@lem3761887 A s f h1) (fun x : A => fun h0 : term922 A s f x => @lem3768908 A x s f h0 h2)). Qed.
Lemma lem3768910 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term557 A s f) (h2 : term513 A s f) : (term557 A s f) = False.
Proof. exact (prop_ext (fun h3 : term557 A s f => @lem3768909 A s f h1 h2) (fun h3 : False => @lem3760357 A s f h1)). Qed.
Lemma lem3768911 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term557 A s f) (h2 : term513 A s f) : False.
Proof. exact (EQ_MP (@lem3768910 A s f h1 h2) (@lem3760357 A s f h1)). Qed.
Lemma lem3768912 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term513 A s f) : term556 A s f.
Proof. exact (fun h0 : term557 A s f => @lem3768911 A s f h0 h1). Qed.
Lemma lem3768913 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term513 A s f) : term540 A s f.
Proof. exact (EQ_MP (@lem3760356 A s f) (@lem3768912 A s f h1)). Qed.
Lemma lem3768914 {A : Type'} (s : A -> Prop) (f : type686 A) : term541 A s f.
Proof. exact (fun h0 : term513 A s f => @lem3768913 A s f h0). Qed.
Lemma lem3768919 {A : Type'} (f : type686 A) : term551 A f.
Proof. exact (fun s : A -> Prop => @lem3768914 A s f). Qed.
Lemma lem3768924 {A : Type'} : term555 A.
Proof. exact (fun f : type686 A => @lem3768919 A f). Qed.
Lemma lem3768925 {A : Type'} : term554 A.
Proof. exact (EQ_MP (@lem3760351 A) (@lem3768924 A)). Qed.
Lemma lem3768926 {A : Type'} (f : type686 A) : term1102 A f.
Proof. exact (@lem3768925 A f). Qed.
Lemma lem3768927 {A : Type'} (f : type686 A) : (term1102 A f) = (term550 A f).
Proof. exact (eq_refl (term1102 A f)). Qed.
Lemma lem3768928 {A : Type'} (f : type686 A) : term550 A f.
Proof. exact (EQ_MP (@lem3768927 A f) (@lem3768926 A f)). Qed.
Lemma lem3768929 {A : Type'} (f : type686 A) (s : A -> Prop) : term1103 A f s.
Proof. exact (@lem3768928 A f s). Qed.
Lemma lem3768930 {A : Type'} (s : A -> Prop) (f : type686 A) : (term1103 A f s) = (term542 A s f).
Proof. exact (eq_refl (term1103 A f s)). Qed.
Lemma lem3768931 {A : Type'} (s : A -> Prop) (f : type686 A) : term542 A s f.
Proof. exact (EQ_MP (@lem3768930 A s f) (@lem3768929 A f s)). Qed.
Lemma lem3768933 {A : Type'} (s : A -> Prop) (f : type686 A) : term542 A s f.
Proof. exact (@lem3759819 A s f (@lem3768931 A s f)). Qed.
Lemma lem3768934 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term543 A s f) : False.
Proof. exact (@lem3768933 A s f (@lem3759803 A s f h1)). Qed.
Lemma lem3768935 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term543 A s f) : (term543 A s f) = False.
Proof. exact (prop_ext (fun h2 : term543 A s f => @lem3768934 A s f h1) (fun h2 : False => @lem3759803 A s f h1)). Qed.
Lemma lem3768936 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term543 A s f) : False.
Proof. exact (EQ_MP (@lem3768935 A s f h1) (@lem3759803 A s f h1)). Qed.
Lemma lem3768937 {A : Type'} (s : A -> Prop) (f : type686 A) : term542 A s f.
Proof. exact (fun h0 : term543 A s f => @lem3768936 A s f h0). Qed.
Lemma lem3768938 {A : Type'} (s : A -> Prop) (f : type686 A) : term541 A s f.
Proof. exact (EQ_MP (@lem3759802 A s f) (@lem3768937 A s f)). Qed.
Lemma lem3768939 {A : Type'} (s : A -> Prop) (f : type686 A) : term481 A s f.
Proof. exact (EQ_MP (@lem3759798 A s f) (@lem3768938 A s f)). Qed.
Lemma lem3768940 {A : Type'} (s : A -> Prop) (f : type686 A) : term480 A s f.
Proof. exact (EQ_MP (@lem3759303 A s f) (@lem3768939 A s f)). Qed.
Lemma lem3768941 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : @SUBSET A s s) : term478 A s f.
Proof. exact (@lem3768940 A s f (@lem3759039 A f s h1 h2 h3 h4 h5)). Qed.
Lemma lem3768942 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : @SUBSET A s s) : term430 A s f.
Proof. exact (@lem3759025 A s f (@lem3768941 A f s h1 h2 h3 h4 h5)). Qed.
Lemma lem3768943 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : @SUBSET A s s) : term429 A s f.
Proof. exact (EQ_MP (@lem3759021 A s f h1) (@lem3768942 A f s h1 h2 h3 h4 h5)). Qed.
Lemma lem3768944 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : term270 A f) (h6 : @SUBSET A s s) : term412 A s f.
Proof. exact (@lem3768943 A f s h1 h2 h3 h4 h6 (@lem3758946 A f h5)). Qed.
Lemma lem3768945 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term381 A s f) : term380 A s f.
Proof. exact (proj2 (@lem3758947 A s f h1)). Qed.
Lemma lem3768946 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term381 A s f) : term334 A f s.
Proof. exact (proj1 (@lem3758947 A s f h1)). Qed.
Lemma lem3768947 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term380 A s f) : term268 A f.
Proof. exact (proj2 (@lem3758948 A s f h1)). Qed.
Lemma lem3768948 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term380 A s f) : term375 A f s.
Proof. exact (proj1 (@lem3758948 A s f h1)). Qed.
Lemma lem3768949 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : term270 A f) (h6 : @SUBSET A s s) : (term268 A f) = (term412 A s f).
Proof. exact (prop_ext (fun h7 : term268 A f => @lem3768944 A f s h1 h2 h3 h4 h5 h6) (fun h7 : term412 A s f => @lem3758952 A f h1)). Qed.
Lemma lem3768950 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : term270 A f) (h6 : @SUBSET A s s) : term412 A s f.
Proof. exact (EQ_MP (@lem3768949 A f s h1 h2 h3 h4 h5 h6) (@lem3758952 A f h1)). Qed.
Lemma lem3768951 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : term270 A f) (h6 : @SUBSET A s s) : (term375 A f s) = (term412 A s f).
Proof. exact (prop_ext (fun h7 : term375 A f s => @lem3768950 A f s h1 h2 h3 h4 h5 h6) (fun h7 : term412 A s f => @lem3758953 A f s h2)). Qed.
Lemma lem3768952 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term268 A f) (h2 : term375 A f s) (h3 : term265 A f s) (h4 : term112 A f) (h5 : term270 A f) (h6 : @SUBSET A s s) : term412 A s f.
Proof. exact (EQ_MP (@lem3768951 A f s h1 h2 h3 h4 h5 h6) (@lem3758953 A f s h2)). Qed.
Lemma lem3768953 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term375 A f s) (h2 : term265 A f s) (h3 : term112 A f) (h4 : term380 A s f) (h5 : term270 A f) (h6 : @SUBSET A s s) : (term268 A f) = (term412 A s f).
Proof. exact (prop_ext (fun h7 : term268 A f => @lem3768952 A f s h7 h1 h2 h3 h5 h6) (fun h7 : term412 A s f => @lem3768947 A s f h4)). Qed.
Lemma lem3768954 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term375 A f s) (h2 : term265 A f s) (h3 : term112 A f) (h4 : term380 A s f) (h5 : term270 A f) (h6 : @SUBSET A s s) : term412 A s f.
Proof. exact (EQ_MP (@lem3768953 A f s h1 h2 h3 h4 h5 h6) (@lem3768947 A s f h4)). Qed.
Lemma lem3768955 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term265 A f s) (h2 : term112 A f) (h3 : term380 A s f) (h4 : term270 A f) (h5 : @SUBSET A s s) : (term375 A f s) = (term412 A s f).
Proof. exact (prop_ext (fun h6 : term375 A f s => @lem3768954 A f s h6 h1 h2 h3 h4 h5) (fun h6 : term412 A s f => @lem3768948 A s f h3)). Qed.
Lemma lem3768956 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term265 A f s) (h2 : term112 A f) (h3 : term380 A s f) (h4 : term270 A f) (h5 : @SUBSET A s s) : term412 A s f.
Proof. exact (EQ_MP (@lem3768955 A f s h1 h2 h3 h4 h5) (@lem3768948 A s f h3)). Qed.
Lemma lem3768957 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term334 A f s) : term265 A f s.
Proof. exact (proj2 (@lem3758949 A f s h1)). Qed.
Lemma lem3768958 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term334 A f s) : @SUBSET A s s.
Proof. exact (proj1 (@lem3758949 A f s h1)). Qed.
Lemma lem3768959 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term265 A f s) (h2 : term112 A f) (h3 : term380 A s f) (h4 : term270 A f) (h5 : @SUBSET A s s) : (term265 A f s) = (term412 A s f).
Proof. exact (prop_ext (fun h6 : term265 A f s => @lem3768956 A f s h1 h2 h3 h4 h5) (fun h6 : term412 A s f => @lem3758950 A f s h1)). Qed.
Lemma lem3768960 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term265 A f s) (h2 : term112 A f) (h3 : term380 A s f) (h4 : term270 A f) (h5 : @SUBSET A s s) : term412 A s f.
Proof. exact (EQ_MP (@lem3768959 A f s h1 h2 h3 h4 h5) (@lem3758950 A f s h1)). Qed.
Lemma lem3768961 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term265 A f s) (h2 : term112 A f) (h3 : term380 A s f) (h4 : term270 A f) (h5 : @SUBSET A s s) : (@SUBSET A s s) = (term412 A s f).
Proof. exact (prop_ext (fun h6 : @SUBSET A s s => @lem3768960 A f s h1 h2 h3 h4 h5) (fun h6 : term412 A s f => @lem3758951 A s h5)). Qed.
Lemma lem3768962 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term265 A f s) (h2 : term112 A f) (h3 : term380 A s f) (h4 : term270 A f) (h5 : @SUBSET A s s) : term412 A s f.
Proof. exact (EQ_MP (@lem3768961 A f s h1 h2 h3 h4 h5) (@lem3758951 A s h5)). Qed.
Lemma lem3768963 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term112 A f) (h2 : term380 A s f) (h3 : term334 A f s) (h4 : term270 A f) (h5 : @SUBSET A s s) : (term265 A f s) = (term412 A s f).
Proof. exact (prop_ext (fun h6 : term265 A f s => @lem3768962 A f s h6 h1 h2 h4 h5) (fun h6 : term412 A s f => @lem3768957 A f s h3)). Qed.
Lemma lem3768964 {A : Type'} (f : type686 A) (s : A -> Prop) (h1 : term112 A f) (h2 : term380 A s f) (h3 : term334 A f s) (h4 : term270 A f) (h5 : @SUBSET A s s) : term412 A s f.
Proof. exact (EQ_MP (@lem3768963 A f s h1 h2 h3 h4 h5) (@lem3768957 A f s h3)). Qed.
Lemma lem3768965 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) (h2 : term380 A s f) (h3 : term334 A f s) (h4 : term270 A f) : (@SUBSET A s s) = (term412 A s f).
Proof. exact (prop_ext (fun h5 : @SUBSET A s s => @lem3768964 A f s h1 h2 h3 h4 h5) (fun h5 : term412 A s f => @lem3768958 A f s h3)). Qed.
Lemma lem3768966 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) (h2 : term380 A s f) (h3 : term334 A f s) (h4 : term270 A f) : term412 A s f.
Proof. exact (EQ_MP (@lem3768965 A s f h1 h2 h3 h4) (@lem3768958 A f s h3)). Qed.
Lemma lem3768967 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) (h2 : term381 A s f) (h3 : term334 A f s) (h4 : term270 A f) : (term380 A s f) = (term412 A s f).
Proof. exact (prop_ext (fun h5 : term380 A s f => @lem3768966 A s f h1 h5 h3 h4) (fun h5 : term412 A s f => @lem3768945 A s f h2)). Qed.
Lemma lem3768968 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) (h2 : term381 A s f) (h3 : term334 A f s) (h4 : term270 A f) : term412 A s f.
Proof. exact (EQ_MP (@lem3768967 A s f h1 h2 h3 h4) (@lem3768945 A s f h2)). Qed.
Lemma lem3768969 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) (h2 : term381 A s f) (h3 : term270 A f) : (term334 A f s) = (term412 A s f).
Proof. exact (prop_ext (fun h4 : term334 A f s => @lem3768968 A s f h1 h2 h4 h3) (fun h4 : term412 A s f => @lem3768946 A s f h2)). Qed.
Lemma lem3768970 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) (h2 : term381 A s f) (h3 : term270 A f) : term412 A s f.
Proof. exact (EQ_MP (@lem3768969 A s f h1 h2 h3) (@lem3768946 A s f h2)). Qed.
Lemma lem3768971 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) (h2 : term270 A f) : term421 A s f.
Proof. exact (fun h0 : term381 A s f => @lem3768970 A s f h1 h0 h2). Qed.
Lemma lem3768972 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) : term422 A s f.
Proof. exact (fun h0 : term270 A f => @lem3768971 A s f h1 h0). Qed.
Lemma lem3768973 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term112 A f) : term385 A s f.
Proof. exact (EQ_MP (@lem3758945 A s f h1) (@lem3768972 A s f h1)). Qed.
Lemma lem3768974 {A : Type'} (s : A -> Prop) (f : type686 A) : term385 A s f.
Proof. exact (or_elim (@lem3757298 A f) (fun h0 : f = (@EMPTY (A -> Prop)) => @lem3758808 A s f h0) (fun h0 : term112 A f => @lem3768973 A s f h0)). Qed.
Lemma lem3768979 {A : Type'} (s : A -> Prop) : term387 A s.
Proof. exact (fun f : type686 A => @lem3768974 A s f). Qed.
Lemma lem3768984 {A : Type'} : term389 A.
Proof. exact (fun s : A -> Prop => @lem3768979 A s). Qed.
Lemma lem3768985 {A : Type'} : term353 A.
Proof. exact (EQ_MP (@lem3758502 A) (@lem3768984 A)). Qed.
Lemma lem3768986 {A : Type'} : term215 A.
Proof. exact (EQ_MP (@lem3758296 A) (@lem3768985 A)). Qed.
Lemma lem3768987 {A : Type'} : term191 A.
Proof. exact (@lem3757581 A (@lem3768986 A)). Qed.
Lemma lem3768988 {A : Type'} : term190 A.
Proof. exact (EQ_MP (@lem3757552 A) (@lem3768987 A)). Qed.
