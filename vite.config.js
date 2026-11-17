import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'
import tailwindcss from '@tailwindcss/vite'

export default defineConfig({
  // Relative asset paths, so that the build works in any directory of the server.
  base: './',
  plugins: [react(), tailwindcss()],
  build: {
    rolldownOptions: {
      output: {
        // The fonts go to dist/fonts instead of dist/assets. Their names change only if
        // the font files themselves change, so dist/assets can be uploaded on its own.
        assetFileNames: (asset) => {
          const name = asset.names?.[0] ?? asset.name ?? ''
          return /\.(woff2?|ttf|otf|eot)$/i.test(name) ? 'fonts/[name]-[hash][extname]' : 'assets/[name]-[hash][extname]'
        },
      },
    },
  },
})