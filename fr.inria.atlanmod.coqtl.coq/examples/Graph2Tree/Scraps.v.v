Definition test1 ( n : nat): option nat := 
match n with
| 0 => None
| S n' => Some 1
end.



Definition Graph2Tree' :=
  transformation Graph2Tree decreases v from GraphMetamodel to GraphMetamodel
    with m as GraphModel := [
      rule Node2Node
        from
          n class NodeEClass
        for
          i in (allPathsTo m 2 n)
        to [
          "n" :
            n' class NodeEClass :=
match v with
| 0 => BuildNode newId (getNodeName n)
| S v' => BuildNode newId ((getNodeName n) ++ "___error"%string ++ (natToString (length (Graph2Tree (v') (fun c:GraphModel => nil) (Build_Model nil nil)))))
end
              
            with [
              ref NodeEdgesEReference :=
                pth <- i; 
                children <- getNodeEdges n m;
                iters <- Some (map (app pth) (singletons children));
                match v with
| 0 => None
| 1 => a <- nth_error children 0;
b <- nth_error iters 0;
c <- resolveIter2 (parseTransformation (Graph2Tree 0)) m "n" NodeEClass [[a]] b;
                return BuildNodeEdges n' c::nil
end


            ]
        ]
    ].