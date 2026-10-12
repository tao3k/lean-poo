import LeanPoo.Prototype.AVL

namespace LeanPoo.Prototype
variable {Key Value : Type}

theorem avlMake_correct (left right output : Tree Key Value) (key : Key) (value : Value)
    (leftValid : left.ValidAVL) (rightValid : right.ValidAVL)
    (success : avlMake left key value right = .ok output) :
    output.ValidAVL ∧ output.inorder = left.inorder ++ [(key,value)] ++ right.inorder ∧
      output.height = 1 + max left.height right.height := by
  simp only [avlMake, left.cachedHeight_valid leftValid, right.cachedHeight_valid rightValid,
    bind, Except.bind] at success
  split at success
  · simp [throw, throwThe] at success
  · rename_i balanced
    simp only [pure, Except.pure, Except.ok.injEq] at success
    subst output
    have bounds : left.height ≤ right.height+1 ∧ right.height ≤ left.height+1 := by
      simp at balanced
      exact ⟨by omega, by omega⟩
    exact ⟨⟨leftValid, rightValid, rfl, bounds⟩, rfl, rfl⟩

theorem avlMake_complete (left right : Tree Key Value) (key : Key) (value : Value)
    (leftValid : left.ValidAVL) (rightValid : right.ValidAVL)
    (leftBound : left.height ≤ right.height+1) (rightBound : right.height ≤ left.height+1) :
    avlMake left key value right =
      .ok (.node left key value (some (1 + max left.height right.height)) right) := by
  simp [avlMake, left.cachedHeight_valid leftValid, right.cachedHeight_valid rightValid,
    show ¬left.height > right.height+1 by omega,
    show ¬right.height > left.height+1 by omega, bind, Except.bind, pure, Except.pure]

/-- Rebuilding never changes keys or values, even when heights are rejected. -/
theorem avlMake_contents (left right output : Tree Key Value) (key : Key) (value : Value)
    (success : avlMake left key value right = .ok output) :
    output.inorder = left.inorder ++ [(key,value)] ++ right.inorder := by
  unfold avlMake at success
  cases lh : left.cachedHeight <;> cases rh : right.cachedHeight <;>
    simp only [lh, rh, bind, Except.bind] at success
  all_goals try { simp [throw, throwThe] at success }
  split at success
  · simp [throw, throwThe] at success
  · simp only [pure, Except.pure, Except.ok.injEq] at success
    subst output; rfl

/-- The source single right rotation preserves the entire in-order dictionary,
including stored values, without any assumptions on key comparisons. -/
theorem rotate_right_contents (ll lr right : Tree Key Value) (lk key : Key) (lv value : Value)
    (inner outer : Option Nat) :
    (Tree.node ll lk lv outer (.node lr key value inner right)).inorder =
      ll.inorder ++ [(lk,lv)] ++ lr.inorder ++ [(key,value)] ++ right.inorder := by
  simp [Tree.inorder, List.append_assoc]

theorem rotate_left_contents (left rl rr : Tree Key Value) (key rk : Key) (value rv : Value)
    (inner outer : Option Nat) :
    (Tree.node (.node left key value inner rl) rk rv outer rr).inorder =
      left.inorder ++ [(key,value)] ++ rl.inorder ++ [(rk,rv)] ++ rr.inorder := by
  simp [Tree.inorder, List.append_assoc]

private theorem make_right (a b c output : Tree Key Value) (x y : Key) (vx vy : Value)
    (va : a.ValidAVL) (vb : b.ValidAVL) (vc : c.ValidAVL)
    (success : (do avlMake a x vx (← avlMake b y vy c)) = .ok output) :
    output.ValidAVL ∧ output.inorder = a.inorder ++ [(x,vx)] ++ b.inorder ++ [(y,vy)] ++ c.inorder := by
  cases inner : avlMake b y vy c with
  | error message => simp [inner, bind, Except.bind] at success
  | ok middle =>
    simp only [inner, bind, Except.bind] at success
    have first := avlMake_correct b c middle y vy vb vc inner
    have second := avlMake_correct a middle output x vx va first.1 success
    exact ⟨second.1, by simp [second.2.1, first.2.1, List.append_assoc]⟩

private theorem make_left (a b c output : Tree Key Value) (x y : Key) (vx vy : Value)
    (va : a.ValidAVL) (vb : b.ValidAVL) (vc : c.ValidAVL)
    (success : (do avlMake (← avlMake a x vx b) y vy c) = .ok output) :
    output.ValidAVL ∧ output.inorder = a.inorder ++ [(x,vx)] ++ b.inorder ++ [(y,vy)] ++ c.inorder := by
  cases inner : avlMake a x vx b with
  | error message => simp [inner, bind, Except.bind] at success
  | ok middle =>
    simp only [inner, bind, Except.bind] at success
    have first := avlMake_correct a b middle x vx va vb inner
    have second := avlMake_correct middle c output y vy first.1 vc success
    exact ⟨second.1, by simp [second.2.1, first.2.1, List.append_assoc]⟩

private theorem make_both (a b c d output : Tree Key Value) (x y z : Key) (vx vy vz : Value)
    (va : a.ValidAVL) (vb : b.ValidAVL) (vc : c.ValidAVL) (vd : d.ValidAVL)
    (success : (do avlMake (← avlMake a x vx b) y vy (← avlMake c z vz d)) = .ok output) :
    output.ValidAVL ∧ output.inorder = a.inorder ++ [(x,vx)] ++ b.inorder ++ [(y,vy)] ++
      c.inorder ++ [(z,vz)] ++ d.inorder := by
  cases left : avlMake a x vx b with
  | error message => simp [left, bind, Except.bind] at success
  | ok first =>
    cases right : avlMake c z vz d with
    | error message => simp [left, right, bind, Except.bind] at success
    | ok second =>
      simp only [left, right, bind, Except.bind] at success
      have firstCorrect := avlMake_correct a b first x vx va vb left
      have secondCorrect := avlMake_correct c d second z vz vc vd right
      have finalCorrect := avlMake_correct first second output y vy firstCorrect.1 secondCorrect.1 success
      exact ⟨finalCorrect.1, by simp [finalCorrect.2.1, firstCorrect.2.1, secondCorrect.2.1, List.append_assoc]⟩

private theorem contents_right (a b c output : Tree Key Value) (x y : Key) (vx vy : Value)
    (success : (do avlMake a x vx (← avlMake b y vy c)) = .ok output) :
    output.inorder = a.inorder ++ [(x,vx)] ++ b.inorder ++ [(y,vy)] ++ c.inorder := by
  cases inner : avlMake b y vy c with
  | error message => simp [inner, bind, Except.bind] at success
  | ok middle =>
    simp only [inner, bind, Except.bind] at success
    have first := avlMake_contents b c middle y vy inner
    have second := avlMake_contents a middle output x vx success
    simp [second, first, List.append_assoc]

private theorem contents_left (a b c output : Tree Key Value) (x y : Key) (vx vy : Value)
    (success : (do avlMake (← avlMake a x vx b) y vy c) = .ok output) :
    output.inorder = a.inorder ++ [(x,vx)] ++ b.inorder ++ [(y,vy)] ++ c.inorder := by
  cases inner : avlMake a x vx b with
  | error message => simp [inner, bind, Except.bind] at success
  | ok middle =>
    simp only [inner, bind, Except.bind] at success
    have first := avlMake_contents a b middle x vx inner
    have second := avlMake_contents middle c output y vy success
    simp [second, first, List.append_assoc]

private theorem contents_both (a b c d output : Tree Key Value) (x y z : Key) (vx vy vz : Value)
    (success : (do avlMake (← avlMake a x vx b) y vy (← avlMake c z vz d)) = .ok output) :
    output.inorder = a.inorder ++ [(x,vx)] ++ b.inorder ++ [(y,vy)] ++
      c.inorder ++ [(z,vz)] ++ d.inorder := by
  cases left : avlMake a x vx b with
  | error message => simp [left, bind, Except.bind] at success
  | ok first =>
    cases right : avlMake c z vz d with
    | error message => simp [left, right, bind, Except.bind] at success
    | ok second =>
      simp only [left, right, bind, Except.bind] at success
      have firstCorrect := avlMake_contents a b first x vx left
      have secondCorrect := avlMake_contents c d second z vz right
      have finalCorrect := avlMake_contents first second output y vy success
      simp [finalCorrect, firstCorrect, secondCorrect, List.append_assoc]

/-- Every successful source rotation preserves AVL validity, exact cached
heights and the entire in-order key/value sequence. This includes all four
rotation cases and makes no assumptions about the values stored at keys. -/
theorem Dictionary.avlNode_preserves (left right output : Tree Key Value) (key : Key) (value : Value)
    (leftValid : left.ValidAVL) (rightValid : right.ValidAVL)
    (success : Dictionary.avlNode left key value right = .ok output) :
    output.ValidAVL ∧ output.inorder = left.inorder ++ [(key,value)] ++ right.inorder := by
  simp only [Dictionary.avlNode, left.cachedHeight_valid leftValid,
    right.cachedHeight_valid rightValid, bind, Except.bind, pure, Except.pure] at success
  split at success
  · exact (avlMake_correct left right output key value leftValid rightValid success).imp_right
      (fun result => result.1)
  · split at success
    · cases left with
      | empty => simp [throw, throwThe] at success
      | node ll lk lv cached lr =>
        have vl := leftValid.1
        have vr := leftValid.2.1
        simp only [Tree.cachedHeight_valid ll vl, Tree.cachedHeight_valid lr vr, bind, Except.bind] at success
        split at success
        · simpa [Tree.inorder, List.append_assoc] using make_right ll lr right output lk key lv value vl vr rightValid success
        · split at success
          · cases lr with
            | empty => simp [throw, throwThe] at success
            | node lrl lrk lrv cached lrr =>
              simpa [Tree.inorder, List.append_assoc] using make_both ll lrl lrr right output lk lrk key lv lrv value
                vl vr.1 vr.2.1 rightValid success
          · simp [throw, throwThe] at success
    · split at success
      · cases right with
        | empty => simp [throw, throwThe] at success
        | node rl rk rv cached rr =>
          have vl := rightValid.1
          have vr := rightValid.2.1
          simp only [Tree.cachedHeight_valid rl vl, Tree.cachedHeight_valid rr vr, bind, Except.bind] at success
          split at success
          · cases rl with
            | empty => simp [throw, throwThe] at success
            | node rll rlk rlv cached rlr =>
              simpa [Tree.inorder, List.append_assoc] using make_both left rll rlr rr output key rlk rk value rlv rv
                leftValid vl.1 vl.2.1 vr success
          · split at success
            · simpa [Tree.inorder, List.append_assoc] using make_left left rl rr output key rk value rv leftValid vl vr success
            · simp [throw, throwThe] at success
      · simp [throw, throwThe] at success

theorem Dictionary.avlNode_contents (left right output : Tree Key Value) (key : Key) (value : Value)
    (success : Dictionary.avlNode left key value right = .ok output) :
    output.inorder = left.inorder ++ [(key,value)] ++ right.inorder := by
  unfold Dictionary.avlNode at success
  cases lh : left.cachedHeight <;> cases rh : right.cachedHeight <;>
    simp only [lh, rh, bind, Except.bind, pure, Except.pure] at success
  all_goals try { simp [throw, throwThe] at success }
  split at success
  · exact avlMake_contents left right output key value success
  · split at success
    · cases left with
      | empty => simp [throw, throwThe] at success
      | node ll lk lv cached lr =>
        cases llh : ll.cachedHeight <;> cases lrh : lr.cachedHeight <;>
          simp only [llh, lrh, bind, Except.bind] at success
        all_goals try { simp [throw, throwThe] at success }
        split at success
        · simpa [Tree.inorder, List.append_assoc] using contents_right ll lr right output lk key lv value success
        · split at success
          · cases lr with
            | empty => simp [throw, throwThe] at success
            | node lrl lrk lrv cached lrr =>
              simpa [Tree.inorder, List.append_assoc] using contents_both ll lrl lrr right output lk lrk key lv lrv value
                success
          · simp [throw, throwThe] at success
    · split at success
      · cases right with
        | empty => simp [throw, throwThe] at success
        | node rl rk rv cached rr =>
          cases rlh : rl.cachedHeight <;> cases rrh : rr.cachedHeight <;>
            simp only [rlh, rrh, bind, Except.bind] at success
          all_goals try { simp [throw, throwThe] at success }
          split at success
          · cases rl with
            | empty => simp [throw, throwThe] at success
            | node rll rlk rlv cached rlr =>
              simpa [Tree.inorder, List.append_assoc] using contents_both left rll rlr rr output key rlk rk value rlv rv
                success
          · split at success
            · simpa [Tree.inorder, List.append_assoc] using contents_left left rl rr output key rk value rv success
            · simp [throw, throwThe] at success
      · simp [throw, throwThe] at success

private def balancedNode (left : Tree Key Value) (key : Key) (value : Value) (right : Tree Key Value) : Tree Key Value :=
  .node left key value (some (1 + max left.height right.height)) right

private theorem balancedNode_valid (left right : Tree Key Value) (key : Key) (value : Value)
    (vl : left.ValidAVL) (vr : right.ValidAVL)
    (bl : left.height ≤ right.height+1) (br : right.height ≤ left.height+1) :
    (balancedNode left key value right).ValidAVL := ⟨vl, vr, rfl, bl, br⟩

/-- Valid children differing by at most two always admit one of the source
rotation cases. The resulting height is the old maximum or one greater;
already balanced children need no rotation and have the exact node height. -/
theorem Dictionary.avlNode_complete (left right : Tree Key Value) (key : Key) (value : Value)
    (leftValid : left.ValidAVL) (rightValid : right.ValidAVL)
    (leftBound : left.height ≤ right.height+2) (rightBound : right.height ≤ left.height+2) :
    ∃ output, Dictionary.avlNode left key value right = .ok output ∧
      max left.height right.height ≤ output.height ∧
      output.height ≤ 1 + max left.height right.height ∧
      (left.height ≤ right.height+1 → right.height ≤ left.height+1 →
        output.height = 1 + max left.height right.height) := by
  simp only [Dictionary.avlNode, left.cachedHeight_valid leftValid,
    right.cachedHeight_valid rightValid, bind, Except.bind]
  split
  · rename_i balanced
    have bounds : left.height ≤ right.height+1 ∧ right.height ≤ left.height+1 := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Int.ofNat_eq_natCast, Tree.height] at balanced
      omega
    refine ⟨balancedNode left key value right,
      avlMake_complete left right key value leftValid rightValid bounds.1 bounds.2, ?_⟩
    simp [balancedNode, Tree.height]
  · split
    · rename_i unbalanced delta
      simp only [beq_iff_eq, Int.ofNat_eq_natCast, Tree.height] at delta
      cases left with
      | empty => simp only [Tree.height] at delta; omega
      | node ll lk lv cached lr =>
        have vl := leftValid.1
        have vr := leftValid.2.1
        have childBounds := leftValid.2.2.2
        simp only [Tree.cachedHeight_valid ll vl, Tree.cachedHeight_valid lr vr,
          bind, Except.bind]
        dsimp only [Tree.height] at delta leftBound rightBound
        split
        · rename_i balance
          simp only [Bool.or_eq_true, beq_iff_eq, Int.ofNat_eq_natCast, Tree.height] at balance
          have b1 : lr.height ≤ right.height+1 := by simp only [Int.ofNat_eq_natCast, Tree.height] at *; omega
          have b2 : right.height ≤ lr.height+1 := by simp only [Int.ofNat_eq_natCast, Tree.height] at *; omega
          let middle := balancedNode lr key value right
          have vm := balancedNode_valid lr right key value vr rightValid b1 b2
          have outer1 : ll.height ≤ middle.height+1 := by simp only [middle, balancedNode, Tree.height] at *; omega
          have outer2 : middle.height ≤ ll.height+1 := by simp only [middle, balancedNode, Tree.height] at *; omega
          refine ⟨balancedNode ll lk lv middle, ?_, ?_⟩
          · simp only [avlMake_complete lr right key value vr rightValid b1 b2, bind, Except.bind]
            exact avlMake_complete ll middle lk lv vl vm outer1 outer2
          · simp only [middle, balancedNode, Tree.height] at *; omega
        · split
          · rename_i notSingle balance
            simp only [Bool.or_eq_true, beq_iff_eq, Int.ofNat_eq_natCast, Tree.height] at notSingle
            simp only [beq_iff_eq, Int.ofNat_eq_natCast, Tree.height] at balance
            cases lr with
            | empty => simp only [Tree.height] at balance; omega
            | node lrl lrk lrv cached lrr =>
              have vb := vr.1
              have vc := vr.2.1
              have grandBounds := vr.2.2.2
              dsimp only [Tree.height] at balance delta childBounds
              have b1 : ll.height ≤ lrl.height+1 := by simp only [Int.ofNat_eq_natCast, Tree.height] at *; omega
              have b2 : lrl.height ≤ ll.height+1 := by simp only [Int.ofNat_eq_natCast, Tree.height] at *; omega
              have c1 : lrr.height ≤ right.height+1 := by simp only [Int.ofNat_eq_natCast, Tree.height] at *; omega
              have c2 : right.height ≤ lrr.height+1 := by simp only [Int.ofNat_eq_natCast, Tree.height] at *; omega
              let a := balancedNode ll lk lv lrl
              let b := balancedNode lrr key value right
              have va := balancedNode_valid ll lrl lk lv vl vb b1 b2
              have vb' := balancedNode_valid lrr right key value vc rightValid c1 c2
              have o1 : a.height ≤ b.height+1 := by simp only [a,b,balancedNode,Tree.height] at *; omega
              have o2 : b.height ≤ a.height+1 := by simp only [a,b,balancedNode,Tree.height] at *; omega
              refine ⟨balancedNode a lrk lrv b, ?_, ?_⟩
              · simp only [avlMake_complete ll lrl lk lv vl vb b1 b2,
                  avlMake_complete lrr right key value vc rightValid c1 c2, bind, Except.bind]
                exact avlMake_complete a b lrk lrv va vb' o1 o2
              · simp only [a,b,balancedNode,Tree.height] at *; omega
          · rename_i notSingle notDouble
            simp only [Bool.or_eq_true, beq_iff_eq, Int.ofNat_eq_natCast, Tree.height] at notSingle
            simp only [beq_iff_eq, Int.ofNat_eq_natCast, Tree.height] at notDouble
            omega
    · split
      · rename_i unbalanced notLeft delta
        simp only [beq_iff_eq, Int.ofNat_eq_natCast, Tree.height] at delta
        cases right with
        | empty => simp only [Tree.height] at delta; omega
        | node rl rk rv cached rr =>
          have vl := rightValid.1
          have vr := rightValid.2.1
          have childBounds := rightValid.2.2.2
          simp only [Tree.cachedHeight_valid rl vl, Tree.cachedHeight_valid rr vr,
            bind, Except.bind]
          dsimp only [Tree.height] at delta leftBound rightBound
          split
          · rename_i balance
            simp only [beq_iff_eq, Int.ofNat_eq_natCast, Tree.height] at balance
            cases rl with
            | empty => simp only [Tree.height] at balance; omega
            | node rll rlk rlv cached rlr =>
              have vb := vl.1
              have vc := vl.2.1
              have grandBounds := vl.2.2.2
              dsimp only [Tree.height] at balance delta childBounds
              have b1 : left.height ≤ rll.height+1 := by simp only [Int.ofNat_eq_natCast, Tree.height] at *; omega
              have b2 : rll.height ≤ left.height+1 := by simp only [Int.ofNat_eq_natCast, Tree.height] at *; omega
              have c1 : rlr.height ≤ rr.height+1 := by simp only [Int.ofNat_eq_natCast, Tree.height] at *; omega
              have c2 : rr.height ≤ rlr.height+1 := by simp only [Int.ofNat_eq_natCast, Tree.height] at *; omega
              let a := balancedNode left key value rll
              let b := balancedNode rlr rk rv rr
              have va := balancedNode_valid left rll key value leftValid vb b1 b2
              have vb' := balancedNode_valid rlr rr rk rv vc vr c1 c2
              have o1 : a.height ≤ b.height+1 := by simp only [a,b,balancedNode,Tree.height] at *; omega
              have o2 : b.height ≤ a.height+1 := by simp only [a,b,balancedNode,Tree.height] at *; omega
              refine ⟨balancedNode a rlk rlv b, ?_, ?_⟩
              · simp only [avlMake_complete left rll key value leftValid vb b1 b2,
                  avlMake_complete rlr rr rk rv vc vr c1 c2, bind, Except.bind]
                exact avlMake_complete a b rlk rlv va vb' o1 o2
              · simp only [a,b,balancedNode,Tree.height] at *; omega
          · split
            · rename_i notDouble balance
              simp only [Bool.or_eq_true, beq_iff_eq, Int.ofNat_eq_natCast, Tree.height] at balance
              have b1 : left.height ≤ rl.height+1 := by simp only [Int.ofNat_eq_natCast, Tree.height] at *; omega
              have b2 : rl.height ≤ left.height+1 := by simp only [Int.ofNat_eq_natCast, Tree.height] at *; omega
              let middle := balancedNode left key value rl
              have vm := balancedNode_valid left rl key value leftValid vl b1 b2
              have o1 : middle.height ≤ rr.height+1 := by simp only [middle,balancedNode,Tree.height] at *; omega
              have o2 : rr.height ≤ middle.height+1 := by simp only [middle,balancedNode,Tree.height] at *; omega
              refine ⟨balancedNode middle rk rv rr, ?_, ?_⟩
              · simp only [avlMake_complete left rl key value leftValid vl b1 b2, bind, Except.bind]
                exact avlMake_complete middle rr rk rv vm vr o1 o2
              · simp only [middle,balancedNode,Tree.height] at *; omega
            · rename_i notDouble notSingle
              simp only [Bool.or_eq_true, beq_iff_eq, Int.ofNat_eq_natCast, Tree.height] at notSingle
              simp only [beq_iff_eq, Int.ofNat_eq_natCast, Tree.height] at notDouble
              omega
      · rename_i unbalanced notLeft notRight
        simp only [Bool.and_eq_true, decide_eq_true_eq, Int.ofNat_eq_natCast, Tree.height] at unbalanced
        simp only [beq_iff_eq, Int.ofNat_eq_natCast, Tree.height] at notLeft notRight
        omega

end LeanPoo.Prototype
