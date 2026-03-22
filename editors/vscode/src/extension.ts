// SPDX-License-Identifier: PMPL-1.0-or-later
// VSCode extension for Phronesis language support

import * as path from 'path';
import { workspace, ExtensionContext } from 'vscode';
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind
} from 'vscode-languageclient/node';

let client: LanguageClient;

export function activate(context: ExtensionContext) {
  // Get phronesis executable path from settings
  const config = workspace.getConfiguration('phronesis');
  const serverPath = config.get<string>('serverPath', 'phronesis');

  // Server options - launch phronesis lsp command
  const serverOptions: ServerOptions = {
    command: serverPath,
    args: ['lsp'],
    options: {
      env: process.env
    }
  };

  // Client options
  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: 'file', language: 'phronesis' }],
    synchronize: {
      fileEvents: workspace.createFileSystemWatcher('**/.phr')
    }
  };

  // Create and start the language client
  client = new LanguageClient(
    'phronesis',
    'Phronesis Language Server',
    serverOptions,
    clientOptions
  );

  // Start the client (this will also launch the server)
  client.start();
}

export function deactivate(): Thenable<void> | undefined {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
