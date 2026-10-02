storeSymmetricCharacterTable := function(n)
    local c, f;
    c := CharacterTable("Symmetric", n);
    f := OutputTextFile(Concatenation("charTable_", String(n), ".wl"), false);
    SetPrintFormattingStatus(f, false);
    PrintTo(f, "(* Produced by GAP ", GAPInfo.Version, " *)\n");
    PrintTo(f, "<|\n\"Classes\"->");
    PrintTo(f, "{", JoinStringsWithSeparator(List(CharacterParameters(c), x->Concatenation("{",JoinStringsWithSeparator(x[2]),"}"))), "},\n");
    PrintTo(f, "\"Table\"->");
    PrintTo(f, "{", JoinStringsWithSeparator(List(Irr(c), x->Concatenation("{",JoinStringsWithSeparator(x),"}"))), "}\n");
    PrintTo(f, "|>");
    CloseStream(f);
end;

writeUpTo := function(n)
    local i;
    for i in [1..n] do
        storeSymmetricCharacterTable(i);
    od;
end;
