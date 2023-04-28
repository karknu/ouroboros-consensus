// @ts-check
// Note: type annotations allow type checking and IDEs autocompletion

const lightCodeTheme = require('prism-react-renderer/themes/github');
const darkCodeTheme = require('prism-react-renderer/themes/dracula');

// generic edition URL that will be used by all parts of the documentation
const editUrl = 'https://github.com/input-output-hk/ouroboros-consensus/tree/main/docs/';

/** @type {import('@docusaurus/types').Config} */
const config = {
  title: 'Ouroboros Consensus',
  tagline: 'The family of protocols powering Cardano',
  favicon: 'img/cardano_icon.ico',

  // Set the production url of your site here
  url: 'https://input-output-hk.github.io/',
  // Set the /<baseUrl>/ pathname under which your site is served
  // For GitHub pages deployment, it is often '/<projectName>/'
  baseUrl: '/ouroboros-consensus',

  // GitHub pages deployment config.
  organizationName: 'input-output-hk',
  projectName: 'ouroboros-consensus',

  onBrokenLinks: 'throw',
  onBrokenMarkdownLinks: 'warn',

  // Even if you don't use internalization, you can use this field to set useful
  // metadata like html lang. For example, if your site is Chinese, you may want
  // to replace "en" with "zh-Hans".
  i18n: {
    defaultLocale: 'en',
    locales: ['en'],
  },

  markdown: {
    mermaid: true,
  },

  themes: ['@docusaurus/theme-mermaid'],

  presets: [
    [
      'classic',
      /** @type {import('@docusaurus/preset-classic').Options} */
      ({
        docs: {
          sidebarPath: require.resolve('./sidebars.js'),
          // Please change this to your repo.
          // Remove this to remove the "edit this page" links.
          editUrl,
        },
        theme: {
          customCss: require.resolve('./src/css/custom.css'),
        },
      }),
    ],
  ],

  plugins: [
    [
      "content-docs",
      /** @type {import('@docusaurus/plugin-content-docs').Options} */
      ({
        id: "about-ouroboros",
        path: "about-ouroboros",
        routeBasePath: "about-ouroboros",
        editUrl,
        editLocalizedFiles: true,
      }),
    ],
    [
      "content-docs",
      /** @type {import('@docusaurus/plugin-content-docs').Options} */
      ({
        id: "for-developers",
        path: "for-developers",
        routeBasePath: "for-developers",
        editUrl,
        editLocalizedFiles: true,
      }),
    ],
  ],

  themeConfig:
    /** @type {import('@docusaurus/preset-classic').ThemeConfig} */
    ({
      // Replace with your project's social card
      image: 'img/docusaurus-social-card.jpg',
      prism: {
        additionalLanguages: ['haskell'],
      },
      navbar: {
        title: 'Ouroboros Consensus',
        logo: {
          alt: 'Cardano Logo',
          src: 'img/logo.svg',
        },
        items: [
          {
            to: '/about-ouroboros',
            position: 'left',
            label: 'About Ouroboros',
          },
          {
            to: '/for-developers',
            position: 'left',
            label: 'For Developers',
          },
          {
            type: 'doc',
            docId: 'benchmarks/index',
            position: 'left',
            label: 'Benchmarks',
          },
          {
            href: 'https://github.com/input-output-hk/ouroboros-consensus',
            label: 'GitHub',
            position: 'right',
          },
        ],
      },
      footer: {
        style: 'dark',
        links: [
          {
            title: 'Docs',
            items: [
              {
                label: 'Documentation',
                to: '/docs/Introduction',
              },
              {
                label: 'Benchmarks',
                to: '/docs/benchmarks/',
              },
            ],
          },
          {
            title: 'Community',
            items: [
              {
                label: 'Cardano Updates',
                href: 'https://input-output-hk.github.io/cardano-updates',
              },
              {
                label: 'Stack Overflow',
                href: 'https://cardano.stackexchange.com/questions/tagged/consensus',
              },
              {
                label: 'Discord',
                href: 'https://discord.gg/inputoutput',
              },
            ],
          },
          {
            title: 'More',
            items: [
              {
                label: 'GitHub',
                href: 'https://github.com/input-output-hk/ouroboros-consensus',
              },
              {
                label: 'Haddocks',
                href: 'pathname:///haddocks/index.html',
              },
            ],
          },
        ],
        copyright: `Copyright © ${new Date().getFullYear()} Input Output Global, Built with Docusaurus.`,
      },
      prism: {
        theme: lightCodeTheme,
        darkTheme: darkCodeTheme,
      },
    }),
};

module.exports = config;
