
window.overrideCodeserverActivitybar = function overrideCodeserverActivitybar() {
  return new Promise((resolve, reject) => {
    let isSettled = false;

    function fail(message, error) {
      if (isSettled) return;
      isSettled = true;
      const detail = error ? ` ${error}` : '';
      reject(new Error(`${message}.${detail}`));
    }

    function succeed(details) {
      if (isSettled) return;
      isSettled = true;
      resolve(details);
    }


    const DB_NAME = 'vscode-web-state-db-global';
    const STORE_NAME = 'ItemTable';

    const KEYS = {
      PINNED_VIEWLETS: 'workbench.activity.pinnedViewlets2',
    };

    const PINNED_VIEWLET_IDS = [
      'workbench.view.explorer',
      'workbench.view.extension.ive',
      'workbench.view.extension.continue',
    ];




    /**
     * @param {string | null} rawData
     */
    function updatePinnedViewlets(rawData) {
      const viewlets = rawData ? JSON.parse(rawData) : [];
      const existingIds = new Set(viewlets.map((item) => item.id));

      PINNED_VIEWLET_IDS.forEach((id) => {
        if (!existingIds.has(id)) {
          viewlets.push({ id, pinned: true });
        }
      });

      const updatedViewlets = viewlets.map((item) => ({
        ...item,
        pinned: PINNED_VIEWLET_IDS.includes(item.id),
      }));

      return JSON.stringify(updatedViewlets);
    }




    /**
     * @param {IDBObjectStore} objectStore
     * @param {string} key
     * @param {function(string | null): string} updateFn
     * @param {string} successMsg
     */
    function processIndexedDBUpdate(objectStore, key, updateFn, successMsg) {
      const getRequest = objectStore.get(key);

      getRequest.onerror = (e) => {
        fail(`Get error for key '${key}':`, e.target.error);
      };

      getRequest.onsuccess = () => {
        try {
          const rawData = getRequest.result;
          const newValue = updateFn(rawData);

          if (newValue == null) {
            return;
          }

          const putRequest = objectStore.put(newValue, key);

          putRequest.onsuccess = () => console.log(successMsg);
          putRequest.onerror = (e) => fail(`Put error for key '${key}':`, e.target.error);
        } catch (e) {
          fail(`Data processing failed for key '${key}':`, e);
          objectStore.transaction.abort();
        }
      };
    }



    function runOverrideWithRetry(attempt = 1) {
      const MAX_ATTEMPTS = 10;
      const RETRY_DELAY_MS = 3000;

      const request = indexedDB.open(DB_NAME);

      request.onerror = (event) => {
        fail('Global Database error', event.target.error);
      };

      request.onsuccess = (event) => {
        const db = event.target.result;
        let transaction;

        try {
          transaction = db.transaction([STORE_NAME], 'readwrite');
        } catch (e) {
          if (e && e.name === 'NotFoundError' && attempt < MAX_ATTEMPTS) {
            console.warn(
              `Object store '${STORE_NAME}' not found yet (attempt ${attempt}/${MAX_ATTEMPTS}). Retrying in ${RETRY_DELAY_MS}ms...`,
            );
            db.close();
            setTimeout(() => runOverrideWithRetry(attempt + 1), RETRY_DELAY_MS);
            return;
          }

          fail('Failed to open transaction for activity bar IndexedDB data', e);
          db.close();
          return;
        }

        const objectStore = transaction.objectStore(STORE_NAME);

        processIndexedDBUpdate(
          objectStore,
          KEYS.PINNED_VIEWLETS,
          updatePinnedViewlets,
          `Pinned viewlets '${PINNED_VIEWLET_IDS.join(', ')}' and updated state.`,
        );


        transaction.oncomplete = () => {
          console.log('All IndexedDB updates completed successfully.');
          succeed({ attempt });
          db.close();
        };
        transaction.onerror = (e) => {
          fail('Transaction failed', e.target.error);
          db.close();
        };
      };
    }

    runOverrideWithRetry();
  });
};
