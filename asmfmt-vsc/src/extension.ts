// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import { execSync } from "child_process";
import * as vscode from "vscode";

function formatDocument(document: vscode.TextDocument): vscode.TextEdit[] {
  vscode.window.showInformationMessage("formatting");
  const content = document.getText();
  try {
    const res = execSync("asmfmt", { input: content });

    const firstLine = document.lineAt(0);
    const lastLine = document.lineAt(document.lineCount - 1);
    const range = new vscode.Range(firstLine.range.start, lastLine.range.end);
    return [
      vscode.TextEdit.insert(range.end, res.toString()),
      vscode.TextEdit.delete(range),
    ];
  } catch (error) {
    vscode.window.showErrorMessage("error: " + error);
    console.error(error);
    return [];
  }
}

// This method is called when your extension is activated
// Your extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {
  // Use the console to output diagnostic information (console.log) and errors (console.error)
  // This line of code will only be executed once when your extension is activated
  console.log("loaded");

  vscode.languages.registerDocumentFormattingEditProvider("asm-collection", {
    provideDocumentFormattingEdits(
      document: vscode.TextDocument
    ): vscode.TextEdit[] {
      return formatDocument(document);
    },
  });
}

// This method is called when your extension is deactivated
export function deactivate() {}
