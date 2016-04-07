Option Strict Off
Option Explicit Off

Imports System
Imports EnvDTE
Imports EnvDTE80
Imports EnvDTE90
Imports System.Diagnostics

Public Module VccDemoNewSyntax

    Sub VccDemo1()
        DTE.ActiveDocument.Selection.StartOfDocument()
        DTE.ActiveDocument.Selection.LineDown(False, 4)
        DTE.ActiveDocument.Selection.StartOfLine(vsStartOfLineOptions.vsStartOfLineOptionsFirstColumn)
        DTE.ActiveDocument.Selection.Text = "  _(requires \thread_local_array(buf, len))                   // buf[0..len] is valid, locally owned"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Save()
    End Sub
    Sub VccDemo2()
        DTE.ActiveDocument.Selection.StartOfDocument()
        DTE.ActiveDocument.Selection.LineDown(False, 9)
        DTE.ActiveDocument.Selection.StartOfLine(vsStartOfLineOptions.vsStartOfLineOptionsFirstColumn)
        DTE.ActiveDocument.Selection.Text = "    _(invariant high <= len)"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Save()
    End Sub
    Sub VccDemo3()
        DTE.ActiveDocument.Selection.StartOfDocument()
        DTE.ActiveDocument.Selection.LineDown(False, 5)
        DTE.ActiveDocument.Selection.StartOfLine(vsStartOfLineOptions.vsStartOfLineOptionsFirstColumn)
        DTE.ActiveDocument.Selection.Text = "  _(requires len < INT_MAX)"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Save()
    End Sub

    Sub VccDemo4()
        DTE.ActiveDocument.Selection.StartOfDocument()
        DTE.ActiveDocument.Selection.LineDown(False, 5)
        DTE.ActiveDocument.Selection.EndOfLine(True)
        DTE.ActiveDocument.Selection.Delete()
        DTE.ActiveDocument.Selection.DeleteLeft(1)
        DTE.ActiveDocument.Selection.StartOfLine(vsStartOfLineOptions.vsStartOfLineOptionsFirstColumn)
        DTE.ActiveDocument.Selection.StartOfDocument()
        DTE.ActiveDocument.Selection.LineDown(False, 11)
        DTE.ActiveDocument.Selection.EndOfLine(True)
        DTE.ActiveDocument.Selection.Text = "    mid = low + (high - low) / 2;"
        DTE.ActiveDocument.Save()
    End Sub
    Sub VccDemo4With3Skipped()
        DTE.ActiveDocument.Selection.StartOfDocument()
        DTE.ActiveDocument.Selection.LineDown(False, 11)
        DTE.ActiveDocument.Selection.EndOfLine(True)
        DTE.ActiveDocument.Selection.Text = "    mid = low + (high - low) / 2;"
        DTE.ActiveDocument.Save()
    End Sub
    Sub VccDemo5()
        DTE.ActiveDocument.Selection.StartOfDocument()
        DTE.ActiveDocument.Selection.LineDown(False, 5)
        DTE.ActiveDocument.Selection.StartOfLine(vsStartOfLineOptions.vsStartOfLineOptionsFirstColumn)
        DTE.ActiveDocument.Selection.Text = "  _(ensures \result != UINT_MAX ==> buf[\result] == val)                           // val found"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "  _(ensures \result == UINT_MAX ==> \forall unsigned i; i < len ==> buf[i] != val) // val not found"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Save()
    End Sub
    Sub VccDemo6()
        DTE.ActiveDocument.Selection.StartOfDocument()
        DTE.ActiveDocument.Selection.LineDown(False, 12)
        DTE.ActiveDocument.Selection.StartOfLine(vsStartOfLineOptions.vsStartOfLineOptionsFirstColumn)
        DTE.ActiveDocument.Selection.Text = "    _(invariant \forall unsigned i; i < low              ==> buf[i] <  val) // val isn't to the left of low"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "    _(invariant \forall unsigned i; high <= i && i < len ==> buf[i] >= val) // val isn't to the right of high"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Save()
    End Sub
    Sub VccDemo7()
        DTE.ActiveDocument.Selection.StartOfDocument()
        DTE.ActiveDocument.Selection.LineDown(False, 5)
        DTE.ActiveDocument.Selection.StartOfLine(vsStartOfLineOptions.vsStartOfLineOptionsFirstColumn)
        DTE.ActiveDocument.Selection.Text = "  _(requires \forall unsigned i,j; i < j && j < len ==> buf[i] <= buf[j])          // buffer sorted"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Save()
    End Sub
    Sub VccDemo8()
        DTE.ActiveDocument.Selection.EndOfDocument()
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "/*`"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "Verification of binary_search succeeded."
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "`*/"
        DTE.ActiveDocument.Save()
    End Sub
    Sub ResetDemo()
        DTE.ActiveDocument.Selection.SelectAll()
        DTE.ActiveDocument.Selection.Text = "#include <limits.h>"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "#include <vcc.h>"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "unsigned binary_search(int val, int *buf, unsigned len)"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "{"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "unsigned low, high, mid;"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "low = 0; high = len;"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "while (low < high)"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "{"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "mid = (high + low) / 2;"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "if (buf[mid] < val)             low = mid + 1;"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "else                            high = mid;"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "}"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "if (low < len && buf[low] == val) return low;"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "else                              return UINT_MAX;"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Selection.Text = "}"
        DTE.ActiveDocument.Selection.NewLine()
        DTE.ActiveDocument.Save()
        DTE.ActiveDocument.Selection.LineUp(False, 13)
        DTE.ActiveDocument.Selection.CharLeft(False, 1)
    End Sub
End Module
